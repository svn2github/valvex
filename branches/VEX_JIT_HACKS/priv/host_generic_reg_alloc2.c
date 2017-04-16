
/*---------------------------------------------------------------*/
/*--- begin                                 host_reg_alloc2.c ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2004-2015 OpenWorks LLP
      info@open-works.net

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301, USA.

   The GNU General Public License is contained in the file COPYING.

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.
*/

#include "libvex_basictypes.h"
#include "libvex.h"

#include "main_util.h"
#include "host_generic_regs.h"

/* Set to 1 for lots of debugging output. */
#define DEBUG_REGALLOC 0


/* TODO 27 Oct 04:

   Better consistency checking from what isMove tells us.

   We can possibly do V-V coalescing even when the src is spilled,
   providing we can arrange for the dst to have the same spill slot.

   Note that state[].hreg is the same as the available real regs.

   Generally rationalise data structures.  */


/* Records information on virtual register live ranges.  Computed once
   and remains unchanged after that. */
typedef
   struct {
      /* Becomes live for the first time after this insn ... */
      Short live_after;
      /* Becomes dead for the last time before this insn ... */
      Short dead_before;
      /* The "home" spill slot, if needed.  Never changes. */
      Short spill_offset;
      Short spill_size;
      /* What kind of register this is. */
      HRegClass reg_class;
   }
   VRegLR;


/* Records information on real-register live ranges.  Computed once
   and remains unchanged after that. */
typedef
   struct {
      HReg rreg;
      /* Becomes live after this insn ... */
      Short live_after;
      /* Becomes dead before this insn ... */
      Short dead_before;
   }
   RRegLR;


/* An array of the following structs (rreg_state) comprises the
   running state of the allocator.  It indicates what the current
   disposition of each allocatable real register is.  The array gets
   updated as the allocator processes instructions.  The identity of
   the register is not recorded here, because the index of this
   structure in doRegisterAllocation()'s |rreg_state| is the index
   number of the register, and the register itself can be extracted
   from the RRegUniverse supplied to doRegisterAllocation(). */
typedef
   struct {
      /* ------ FIELDS WHICH DO NOT CHANGE ------ */
      /* Is this involved in any HLRs?  (only an optimisation hint) */
      Bool has_hlrs;
      /* ------ FIELDS WHICH DO CHANGE ------ */
      /* 6 May 07: rearranged fields below so the whole struct fits
         into 16 bytes on both x86 and amd64. */
      /* Used when .disp == Bound and we are looking for vregs to
         spill. */
      Bool is_spill_cand;
      /* Optimisation: used when .disp == Bound.  Indicates when the
         rreg has the same value as the spill slot for the associated
         vreg.  Is safely left at False, and becomes True after a
         spill store or reload for this rreg. */
      Bool eq_spill_slot;
      /* What's it's current disposition? */
      enum { Free,     /* available for use */
             Unavail,  /* in a real-reg live range */
             Bound     /* in use (holding value of some vreg) */
           }
           disp;
      /* If .disp == Bound, what vreg is it bound to? */
      HReg vreg;
   }
   RRegState;


/* The allocator also maintains a redundant array of indexes
   (vreg_state) from vreg numbers back to entries in rreg_state.  It
   is redundant because iff vreg_state[i] == j then
   hregNumber(rreg_state[j].vreg) == i -- that is, the two entries
   point at each other.  The purpose of this is to speed up activities
   which involve looking for a particular vreg: there is no need to
   scan the rreg_state looking for it, just index directly into
   vreg_state.  The FAQ "does this vreg already have an associated
   rreg" is the main beneficiary.  

   To indicate, in vreg_state[i], that a given vreg is not currently
   associated with any rreg, that entry can be set to INVALID_RREG_NO.

   Because the vreg_state entries are signed Shorts, the max number
   of vregs that can be handed by regalloc is 32767.
*/

#define INVALID_RREG_NO ((Short)(-1))

#define IS_VALID_VREGNO(_zz) ((_zz) >= 0 && (_zz) < state->n_vregs)
#define IS_VALID_RREGNO(_zz) ((_zz) >= 0 && (_zz) < state->n_rregs)


/* Search forward from some given point in the incoming instruction
   sequence.  Point is to select a virtual register to spill, by
   finding the vreg which is mentioned as far ahead as possible, in
   the hope that this will minimise the number of consequent reloads.

   Only do the search for vregs which are Bound in the running state,
   and for which the .is_spill_cand field is set.  This allows the
   caller to arbitrarily restrict the set of spill candidates to be
   considered.

   To do this we don't actually need to see the incoming instruction
   stream.  Rather, what we need is the HRegUsage records for the
   incoming instruction stream.  Hence that is passed in.

   Returns an index into the state array indicating the (v,r) pair to
   spill, or -1 if none was found.  */
static
Int findMostDistantlyMentionedVReg ( 
   HRegUsage*   reg_usages_in,
   Int          search_from_instr,
   Int          num_instrs,
   RRegState*   state,
   Int          n_state
)
{
   Int k, m;
   Int furthest_k = -1;
   Int furthest   = -1;
   vassert(search_from_instr >= 0);
   for (k = 0; k < n_state; k++) {
      if (!state[k].is_spill_cand)
         continue;
      vassert(state[k].disp == Bound);
      for (m = search_from_instr; m < num_instrs; m++) {
         if (HRegUsage__contains(&reg_usages_in[m], state[k].vreg))
            break;
      }
      if (m > furthest) {
         furthest   = m;
         furthest_k = k;
      }
   }
   return furthest_k;
}


/* Check that this vreg has been assigned a sane spill offset. */
inline
static void sanity_check_spill_offset ( VRegLR* vreg )
{
   switch (vreg->reg_class) {
      case HRcVec128: case HRcFlt64:
         vassert(0 == ((UShort)vreg->spill_offset % 16)); break;
      default:
         vassert(0 == ((UShort)vreg->spill_offset % 8)); break;
   }
}


/* Double the size of the real-reg live-range array, if needed. */
__attribute__((noinline)) 
static void ensureRRLRspace_SLOW(RRegLR** info, UInt* size, UInt used)
{
   RRegLR* arr2;
   if (0)
      vex_printf("ensureRRLRspace: %u -> %u\n", *size, 2 * *size);
   vassert(used == *size);
   arr2 = LibVEX_Alloc_inline(2 * *size * sizeof(RRegLR));
   for (UInt k = 0; k < *size; k++)
      arr2[k] = (*info)[k];
   *size *= 2;
   *info = arr2;
}
inline
static void ensureRRLRspace(RRegLR** info, UInt* size, UInt used)
{
   if (LIKELY(used < *size)) return;
   ensureRRLRspace_SLOW(info, size, used);
}


/* Sort an array of RRegLR entries by either the .live_after or
   .dead_before fields.  This is performance-critical. */
static void sortRRLRarray ( RRegLR* arr, 
                            UInt size, Bool by_live_after )
{
   Int    incs[14] = { 1, 4, 13, 40, 121, 364, 1093, 3280,
                       9841, 29524, 88573, 265720,
                       797161, 2391484 };
   Int    lo = 0;
   Int    hi = size-1;
   Int    i, j, h, bigN, hp;
   RRegLR v;

   vassert(size >= 0);
   if (size == 0)
      return;

   bigN = hi - lo + 1; if (bigN < 2) return;
   hp = 0; while (hp < 14 && incs[hp] < bigN) hp++; hp--;

   if (by_live_after) {

      for ( ; hp >= 0; hp--) {
         h = incs[hp];
         for (i = lo + h; i <= hi; i++) {
            v = arr[i];
            j = i;
            while (arr[j-h].live_after > v.live_after) {
               arr[j] = arr[j-h];
               j = j - h;
               if (j <= (lo + h - 1)) break;
            }
            arr[j] = v;
         }
      }

   } else {

      for ( ; hp >= 0; hp--) {
         h = incs[hp];
         for (i = lo + h; i <= hi; i++) {
            v = arr[i];
            j = i;
            while (arr[j-h].dead_before > v.dead_before) {
               arr[j] = arr[j-h];
               j = j - h;
               if (j <= (lo + h - 1)) break;
            }
            arr[j] = v;
         }
      }

   }
}


/* Compute the index of the highest and lowest 1 in a ULong,
   respectively.  Results are undefined if the argument is zero.
   Don't pass it zero :) */
static inline UInt ULong__maxIndex ( ULong w64 ) {
   return 63 - __builtin_clzll(w64);
}

static inline UInt ULong__minIndex ( ULong w64 ) {
   return __builtin_ctzll(w64);
}


/* Vectorised memset, copied from Valgrind's m_libcbase.c. */
static void* local_memset ( void *destV, Int c, SizeT sz )
{
#  define IS_4_ALIGNED(aaa_p) (0 == (((HWord)(aaa_p)) & ((HWord)0x3)))

   UInt   c4;
   UChar* d = destV;
   UChar  uc = c;

   while ((!IS_4_ALIGNED(d)) && sz >= 1) {
      d[0] = uc;
      d++;
      sz--;
   }
   if (sz == 0)
      return destV;
   c4 = uc;
   c4 |= (c4 << 8);
   c4 |= (c4 << 16);
   while (sz >= 16) {
      ((UInt*)d)[0] = c4;
      ((UInt*)d)[1] = c4;
      ((UInt*)d)[2] = c4;
      ((UInt*)d)[3] = c4;
      d += 16;
      sz -= 16;
   }
   while (sz >= 4) {
      ((UInt*)d)[0] = c4;
      d += 4;
      sz -= 4;
   }
   while (sz >= 1) {
      d[0] = c;
      d++;
      sz--;
   }
   return destV;

#  undef IS_4_ALIGNED
}

#define N_SPILL64S (LibVEX_N_SPILL_BYTES / 8)
STATIC_ASSERT((N_SPILL64S % 2) == 0);

/* Register allocator state. Keeps all vital information at one place. */
typedef
   struct {
      /* The real-register universe to use.  This contains facts about
         real registers, one of which is the set of registers available
         for allocation. */
      const RRegUniverse* univ;

      /* Info on vregs. Computed once and remains unchanged. */
      UInt    n_vregs;
      VRegLR* vreg_lrs; /* [0 .. n_vregs-1] */

      /* Used when constructing vreg_lrs (for allocating stack slots). */
      Short ss_busy_until_before[N_SPILL64S];

      /* We keep two copies of the real-reg live range info, one sorted
         by .live_after and the other by .dead_before. First the unsorted info
         is created in the _la variant is copied into the _db variant. Once
         that's done both of them are sorted. We also need two integer cursors
         which record the next location in the two arrays to consider. */
      RRegLR* rreg_lrs_la;
      RRegLR* rreg_lrs_db;
      UInt    rreg_lrs_size;
      UInt    rreg_lrs_used;
      UInt    rreg_lrs_la_next;
      UInt    rreg_lrs_db_next;

      /* Info on register usage in the incoming HInstrVec.
         Computed once and remains unchanged, more or less; updated
         sometimes by the direct-reload optimisation. */
      HRegUsage* reg_usage_arr; /* [0 .. instrs_in->insns_used-1] */

      /* Used when constructing rreg_lrs. */
      UInt* rreg_live_after;
      UInt* rreg_dead_before;

      /* Running state of the core allocation algorithm. */
      RRegState* rreg_state;  /* [0 .. n_rregs-1] */
      UInt       n_rregs;

      /* .. and the redundant backward map */
      /* Each value is 0 .. n_rregs-1 or is INVALID_RREG_NO.
        This inplies n_rregs must be <= 32768. */
      Short*     vreg_state;  /* [0 .. n_vregs-1] */

      /* Return True iff the given insn is a reg-reg move, in which
         case also return the src and dst regs. */
      Bool (*isMove)(const HInstr*, HReg*, HReg*);

      /* Get info about register usage in this insn. */
      void (*getRegUsage)(HRegUsage*, const HInstr*, Bool);

      /* Apply a reg-reg mapping to an insn. */
      void (*mapRegs)(HRegRemap*, HInstr*, Bool);

      /* Is this instruction actually HInstrIfThenElse? */
      HInstrIfThenElse* (*isIfThenElse)(const HInstr*);

      /* Return one, or, if we're unlucky, two insn(s) to spill/restore a
         real reg to a spill slot byte offset. The two leading HInstr**
         args are out parameters, through which the generated insns are
         returned. Also (optionally) a 'directReload' function, which
         attempts to replace a given instruction by one which reads
         directly from a specified spill slot. May be NULL, in which
         case the optimisation is not attempted. */
      void    (*genSpill)( HInstr**, HInstr**, HReg, Int, Bool);
      void    (*genReload)( HInstr**, HInstr**, HReg, Int, Bool);
      HInstr* (*directReload)( HInstr*, HReg, Short);
      UInt    guest_sizeB;

      /* For debug printing only. */
      void (*ppInstr)(const HInstr*, Bool);
      void (*ppReg)(HReg);

      /* 32/64bit mode */
      Bool mode64;
   }
   RegAllocState;

#define INVALID_INSTRNO (-2)

static void initRegAllocState(RegAllocState* state, const RRegUniverse* univ,
   Bool (*isMove)(const HInstr*, HReg*, HReg*),
   void (*getRegUsage)(HRegUsage*, const HInstr*, Bool),
   void (*mapRegs)(HRegRemap*, HInstr*, Bool),
   HInstrIfThenElse* (*isIfThenElse)(const HInstr*),
   void (*genSpill)( HInstr**, HInstr**, HReg, Int, Bool),
   void (*genReload)( HInstr**, HInstr**, HReg, Int, Bool),
   HInstr* (*directReload)( HInstr*, HReg, Short),
   UInt guest_sizeB,
   void (*ppInstr)(const HInstr*, Bool), void (*ppReg)(HReg),
   Bool mode64, const HInstrVec* instrs_in, UInt n_vregs)
{
   /* Initialize Register Allocator state. */
   state->univ         = univ;
   state->isMove       = isMove;
   state->getRegUsage  = getRegUsage;
   state->mapRegs      = mapRegs;
   state->isIfThenElse = isIfThenElse;
   state->genSpill     = genSpill;
   state->genReload    = genReload;
   state->directReload = directReload;
   state->guest_sizeB  = guest_sizeB;
   state->ppInstr      = ppInstr;
   state->ppReg        = ppReg;
   state->mode64       = mode64;

   /* n_rregs is no more than a short name for n_available_real_regs. */
   state->n_rregs = univ->allocable;
   state->n_vregs = n_vregs;

   /* If this is not so, vreg_state entries will overflow. */
   vassert(state->n_vregs < 32767);

   /* If this is not so, the universe we have is nonsensical. */
   vassert(state->n_rregs > 0);

   state->rreg_state = LibVEX_Alloc_inline(state->n_rregs * sizeof(RRegState));
   state->vreg_state = LibVEX_Alloc_inline(state->n_vregs * sizeof(Short));

   for (UInt i = 0; i < state->n_rregs; i++) {
      state->rreg_state[i].has_hlrs      = False;
      state->rreg_state[i].disp          = Free;
      state->rreg_state[i].vreg          = INVALID_HREG;
      state->rreg_state[i].is_spill_cand = False;
      state->rreg_state[i].eq_spill_slot = False;
   }

   for (UInt i = 0; i < n_vregs; i++)
      state->vreg_state[i] = INVALID_RREG_NO;


   /* Initialize vreg live ranges. */

   /* This is relatively simple, because (1) we only seek the complete
      end-to-end live range of each vreg, and are not interested in
      any holes in it, and (2) the vregs are conveniently numbered 0
      .. n_vregs-1, so we can just dump the results in a
      pre-allocated array. */

   state->vreg_lrs = NULL;
   if (state->n_vregs > 0)
      state->vreg_lrs = LibVEX_Alloc_inline(sizeof(VRegLR) * state->n_vregs);

   for (UInt i = 0; i < state->n_vregs; i++) {
      state->vreg_lrs[i].live_after   = INVALID_INSTRNO;
      state->vreg_lrs[i].dead_before  = INVALID_INSTRNO;
      state->vreg_lrs[i].spill_offset = 0;
      state->vreg_lrs[i].spill_size   = 0;
      state->vreg_lrs[i].reg_class    = HRcINVALID;
   }

   /* An array to hold the reg-usage info for the incoming instructions. */
   state->reg_usage_arr
      = LibVEX_Alloc_inline(sizeof(HRegUsage) * instrs_in->insns_used-1);


   /* Initialize rreg live ranges. */

   /* This is more complex than previous step, because we need to compute
      exactly all the live ranges of all the allocatable real regs,
      and we don't know in advance how many there will be. */

   state->rreg_lrs_used = 0;
   state->rreg_lrs_size = 4;
   state->rreg_lrs_la
      = LibVEX_Alloc_inline(state->rreg_lrs_size * sizeof(RRegLR));
   state->rreg_lrs_db = NULL; /* Will be created later. */

   /* Track live range start/end points seperately for each rreg. Sigh. */
   vassert(state->n_rregs > 0);
   state->rreg_live_after  = LibVEX_Alloc_inline(state->n_rregs * sizeof(UInt));
   state->rreg_dead_before = LibVEX_Alloc_inline(state->n_rregs * sizeof(UInt));

   for (UInt i = 0; i < state->n_rregs; i++) {
      state->rreg_live_after[i] = state->rreg_dead_before[i] = INVALID_INSTRNO;
   }

   local_memset(state->ss_busy_until_before, 0,
                sizeof(state->ss_busy_until_before));
}

static void print_state(const RegAllocState* state)
{
   for (UInt i = 0; i < state->n_rregs; i++) {
      vex_printf("  rreg_state[%2d] = ", i);
      state->ppReg(state->univ->regs[i]);
      vex_printf("  \t");

      switch (state->rreg_state[i].disp) {
      case Free:    vex_printf("Free\n"); break;
      case Unavail: vex_printf("Unavail\n"); break;
      case Bound:   vex_printf("BoundTo ");
                    state->ppReg(state->rreg_state[i].vreg);
                    vex_printf("\n"); break;
      }
   }

   vex_printf("\n  vreg_state[0 .. %u]:\n    ", state->n_vregs - 1);
   UInt j = 0;
   for (UInt i = 0; i < state->n_vregs; i++) {
      if (state->vreg_state[i] == INVALID_RREG_NO)
         continue;
      vex_printf("[%u] -> %d   ", i, state->vreg_state[i]);
      j++;
      if (j > 0 && (j % 6) == 0)
         vex_printf("\n    ");
   }

   vex_printf("\n");
}

/* A target-independent register allocator.  Requires various
   functions which it uses to deal abstractly with instructions and
   registers, since it cannot have any target-specific knowledge.

   Returns a new vector of instructions, which, as a result of the
   behaviour of mapRegs, will be in-place modifications of the
   original instructions.

   Takes a vector of unallocated insns. Returns a vector of allocated insns.
   Both vectors have the same structure, including any HInstrIfThenElse.
*/
static HInstrVec* regAlloc_HInstrVec(RegAllocState* state,
                                     const HInstrVec* instrs_in)
{
   const Bool eq_spill_opt = True;

   /* The live range numbers are signed shorts, and so limiting the
      number of insns to 15000 comfortably guards against them
      overflowing 32k. */
   /* TODO-JIT: this is incorrect w.r.t. IfThenElse */
   vassert(instrs_in->insns_used <= 15000);

#  define EMIT_INSTR(_instr)                    \
      do {                                      \
        HInstr* _tmp = (_instr);                \
        if (DEBUG_REGALLOC) {                   \
           vex_printf("**  ");                  \
           state->ppInstr(_tmp, state->mode64); \
           vex_printf("\n\n");                  \
        }                                       \
        addHInstr(instrs_out, _tmp);            \
      } while (0)

   /* --------- Stage 0: set up --------- */
   HInstrVec* instrs_out = newHInstrVec();


   /* --------- Stage 1: iterate over instructins --------- */

   /* ------ start of ITERATE OVER INSNS ------ */

   for (UInt ii = 0; ii < instrs_in->insns_used; ii++) {
      const HInstr* instr = instrs_in->insns[ii];

      if (state->isIfThenElse(instr) != NULL) {
         vpanic("IfThenElse unimplemented");
      }

      state->getRegUsage(&state->reg_usage_arr[ii], instr, state->mode64);

      if (0) {
         vex_printf("\n%u  stage1: ", ii);
         state->ppInstr(instr, state->mode64);
         vex_printf("\n");
         ppHRegUsage(state->univ, &state->reg_usage_arr[ii]);
      }

      /* ------ start of DEAL WITH VREG LIVE RANGES ------ */

      /* for each virtual reg mentioned in the insn ... */
      for (UInt j = 0; j < state->reg_usage_arr[ii].n_vRegs; j++) {

         HReg vreg = state->reg_usage_arr[ii].vRegs[j];
         vassert(hregIsVirtual(vreg));

         Int k = hregIndex(vreg);
         if (k < 0 || k >= state->n_vregs) {
            vex_printf("\n");
            state->ppInstr(instr, state->mode64);
            vex_printf("\n");
            vex_printf("vreg %d, n_vregs %u\n", k, state->n_vregs);
            vpanic("regAlloc_HInstrVec: out-of-range vreg");
         }

         /* Take the opportunity to note its regclass.  We'll need
            that when allocating spill slots. */
         if (state->vreg_lrs[k].reg_class == HRcINVALID) {
            /* First mention of this vreg. */
            state->vreg_lrs[k].reg_class = hregClass(vreg);
         } else {
            /* Seen it before, so check for consistency. */
            vassert(state->vreg_lrs[k].reg_class == hregClass(vreg));
         }

         /* Now consider live ranges. */
         switch (state->reg_usage_arr[ii].vMode[j]) {
            case HRmRead: 
               if (state->vreg_lrs[k].live_after == INVALID_INSTRNO) {
                  vex_printf("\n\nOFFENDING VREG = %d\n", k);
                  vpanic("regAlloc_HInstrVec: first event for vreg is Read");
               }
               state->vreg_lrs[k].dead_before = toShort(ii + 1);
               break;
            case HRmWrite:
               if (state->vreg_lrs[k].live_after == INVALID_INSTRNO)
                  state->vreg_lrs[k].live_after = toShort(ii);
               state->vreg_lrs[k].dead_before = toShort(ii + 1);
               break;
            case HRmModify:
               if (state->vreg_lrs[k].live_after == INVALID_INSTRNO) {
                  vex_printf("\n\nOFFENDING VREG = %d\n", k);
                  vpanic("regAlloc_HInstrVec: first event for vreg is Modify");
               }
               state->vreg_lrs[k].dead_before = toShort(ii + 1);
               break;
            default:
               vpanic("regAlloc_HInstrVec(1)");
         } /* switch */

      } /* iterate over virtual registers */

      /* ------ end of DEAL WITH VREG LIVE RANGES ------ */

      /* ------ start of DEAL WITH RREG LIVE RANGES ------ */

      /* If this doesn't hold, the following iteration over real registers
         will fail miserably. */
      STATIC_ASSERT(N_RREGUNIVERSE_REGS == 64);

      const ULong rRead      = state->reg_usage_arr[ii].rRead;
      const ULong rWritten   = state->reg_usage_arr[ii].rWritten;
      const ULong rMentioned = rRead | rWritten;

      UInt rReg_minIndex;
      UInt rReg_maxIndex;
      if (rMentioned == 0) {
         /* There are no real register uses in this insn.  Set
            rReg_{min,max}Index so that the following loop doesn't iterate
            at all, so as to avoid wasting time. */
         rReg_minIndex = 1;
         rReg_maxIndex = 0;
      } else {
         rReg_minIndex = ULong__minIndex(rMentioned);
         rReg_maxIndex = ULong__maxIndex(rMentioned);
         /* Don't bother to look at registers which are not available
            to the allocator.  We asserted above that n_rregs > 0, so
            n_rregs-1 is safe. */
         if (rReg_maxIndex >= state->n_rregs)
            rReg_maxIndex = state->n_rregs-1;
      }

      /* for each allocator-available real reg mentioned in the insn ... */
      /* Note.  We are allocating only over the real regs available to
         the allocator.  Others, eg the stack or baseblock pointers,
         are unavailable to allocation and so we never visit them.
         Hence the iteration is cut off at n_rregs-1, since n_rregs ==
         univ->allocable. */
      for (Int j = rReg_minIndex; j <= rReg_maxIndex; j++) {

         const ULong jMask = 1ULL << j;
         if (LIKELY((rMentioned & jMask) == 0))
            continue;

         const Bool isR = (rRead    & jMask) != 0;
         const Bool isW = (rWritten & jMask) != 0;

         /* Dummy initialisations of flush_la and flush_db to avoid
            possible bogus uninit-var warnings from gcc. */
         Int  flush_la = INVALID_INSTRNO, flush_db = INVALID_INSTRNO;
         Bool flush = False;

         if (isW && !isR) {
            flush_la = state->rreg_live_after[j];
            flush_db = state->rreg_dead_before[j];
            if (flush_la != INVALID_INSTRNO && flush_db != INVALID_INSTRNO)
               flush = True;
            state->rreg_live_after[j]  = ii;
            state->rreg_dead_before[j] = ii+1;
         } else if (!isW && isR) {
            if (state->rreg_live_after[j] == INVALID_INSTRNO) {
               vex_printf("\nOFFENDING RREG = ");
               state->ppReg(state->univ->regs[j]);
               vex_printf("\n");
               vex_printf("\nOFFENDING instr = ");
               state->ppInstr(instr, state->mode64);
               vex_printf("\n");
               vpanic("regAlloc_HInstrVec: first event for rreg is Read");
            }
            state->rreg_dead_before[j] = ii+1;
         } else {
            vassert(isR && isW);
            if (state->rreg_live_after[j] == INVALID_INSTRNO) {
               vex_printf("\nOFFENDING RREG = ");
               state->ppReg(state->univ->regs[j]);
               vex_printf("\n");
               vex_printf("\nOFFENDING instr = ");
               state->ppInstr(instr, state->mode64);
               vex_printf("\n");
               vpanic("regAlloc_HInstrVec: first event for rreg is Modify");
            }
            state->rreg_dead_before[j] = ii+1;
         }

         if (flush) {
            vassert(flush_la != INVALID_INSTRNO);
            vassert(flush_db != INVALID_INSTRNO);
            UInt used = state->rreg_lrs_used;
            ensureRRLRspace(&state->rreg_lrs_la, &state->rreg_lrs_size, used);
            if (0) 
               vex_printf("FLUSH 1 (%d,%d)\n", flush_la, flush_db);
            state->rreg_lrs_la[used].rreg        = state->univ->regs[j];
            state->rreg_lrs_la[used].live_after  = toShort(flush_la);
            state->rreg_lrs_la[used].dead_before = toShort(flush_db);
            state->rreg_lrs_used++;
         }

      } /* iterate over rregs in the instr */

      /* ------ end of DEAL WITH RREG LIVE RANGES ------ */

   } /* iterate over insns */

   /* ------ end of ITERATE OVER INSNS ------ */

   /* ------ start of FINALISE RREG LIVE RANGES ------ */

   /* Now finish up any live ranges left over. */
   for (UInt j = 0; j < state->n_rregs; j++) {

      if (0) {
         vex_printf("residual %u:  %u %u\n", j, state->rreg_live_after[j],
                                                state->rreg_dead_before[j]);
      }
      vassert( (state->rreg_live_after[j] == INVALID_INSTRNO 
                && state->rreg_dead_before[j] == INVALID_INSTRNO)
              ||
               (state->rreg_live_after[j] != INVALID_INSTRNO 
                && state->rreg_dead_before[j] != INVALID_INSTRNO)
            );

      if (state->rreg_live_after[j] == INVALID_INSTRNO)
         continue;

      ensureRRLRspace(&state->rreg_lrs_la, &state->rreg_lrs_size,
                      state->rreg_lrs_used);
      if (0)
         vex_printf("FLUSH 2 (%d,%d)\n", 
                    state->rreg_live_after[j], state->rreg_dead_before[j]);
      UInt used = state->rreg_lrs_used;
      state->rreg_lrs_la[used].rreg        = state->univ->regs[j];
      state->rreg_lrs_la[used].live_after  = toShort(state->rreg_live_after[j]);
      state->rreg_lrs_la[used].dead_before = toShort(state->rreg_dead_before[j]);
      state->rreg_lrs_used++;
   }

   /* Compute summary hints for choosing real regs.  If a real reg is
      involved in a hard live range, record that fact in the fixed
      part of the running rreg_state.  Later, when offered a choice between
      rregs, it's better to choose one which is not marked as having
      any HLRs, since ones with HLRs may need to be spilled around
      their HLRs.  Correctness of final assignment is unaffected by
      this mechanism -- it is only an optimisation. */

   for (UInt j = 0; j < state->rreg_lrs_used; j++) {
      HReg rreg = state->rreg_lrs_la[j].rreg;
      vassert(!hregIsVirtual(rreg));
      /* rreg is involved in a HLR.  Record this info in the array, if
         there is space. */
      UInt ix = hregIndex(rreg);
      vassert(ix < state->n_rregs);
      state->rreg_state[ix].has_hlrs = True;
   }
   if (0) {
      for (UInt j = 0; j < state->n_rregs; j++) {
         if (!state->rreg_state[j].has_hlrs)
            continue;
         state->ppReg(state->univ->regs[j]);
         vex_printf(" hinted\n");
      }
   }

   /* Finally, copy the _la variant into the _db variant and
      sort both by their respective fields. */
   state->rreg_lrs_db
      = LibVEX_Alloc_inline(state->rreg_lrs_used * sizeof(RRegLR));
   for (UInt j = 0; j < state->rreg_lrs_used; j++)
      state->rreg_lrs_db[j] = state->rreg_lrs_la[j];

   sortRRLRarray(state->rreg_lrs_la, state->rreg_lrs_used,
                 True /* by .live_after*/  );
   sortRRLRarray(state->rreg_lrs_db, state->rreg_lrs_used,
                 False/* by .dead_before*/ );

   /* And set up the cursors. */
   state->rreg_lrs_la_next = 0;
   state->rreg_lrs_db_next = 0;

   const RRegLR* lrs_la = state->rreg_lrs_la;
   const RRegLR* lrs_db = state->rreg_lrs_db;
   for (UInt j = 1; j < state->rreg_lrs_used; j++) {
      vassert(lrs_la[j-1].live_after  <= lrs_la[j].live_after);
      vassert(lrs_db[j-1].dead_before <= lrs_db[j].dead_before);
   }

   /* ------ end of FINALISE RREG LIVE RANGES ------ */

   if (DEBUG_REGALLOC) {
      for (UInt j = 0; j < state->n_vregs; j++) {
         vex_printf("vreg %d:  la = %d,  db = %d\n", j,
                    state->vreg_lrs[j].live_after,
                    state->vreg_lrs[j].dead_before );
      }
   }

   if (DEBUG_REGALLOC) {
      vex_printf("RRegLRs by LA:\n");
      for (UInt j = 0; j < state->rreg_lrs_used; j++) {
         vex_printf("  ");
         state->ppReg(state->rreg_lrs_la[j].rreg);
         vex_printf("      la = %d,  db = %d\n",
                    state->rreg_lrs_la[j].live_after,
                    state->rreg_lrs_la[j].dead_before );
      }
      vex_printf("RRegLRs by DB:\n");
      for (UInt j = 0; j < state->rreg_lrs_used; j++) {
         vex_printf("  ");
         state->ppReg(state->rreg_lrs_db[j].rreg);
         vex_printf("      la = %d,  db = %d\n",
                    state->rreg_lrs_db[j].live_after,
                    state->rreg_lrs_db[j].dead_before );
      }
   }

   /* --------- Stage 3: allocate spill slots. --------- */

   /* Each spill slot is 8 bytes long.  For vregs which take more than
      64 bits to spill (classes Flt64 and Vec128), we have to allocate
      two consecutive spill slots.  For 256 bit registers (class
      Vec256), we have to allocate four consecutive spill slots.

      For Vec128-class on PowerPC, the spill slot's actual address
      must be 16-byte aligned.  Since the spill slot's address is
      computed as an offset from the guest state pointer, and since
      the user of the generated code must set that pointer to a
      32-aligned value, we have the residual obligation here of
      choosing a 16-aligned spill slot offset for Vec128-class values.
      Since each spill slot is 8 bytes long, that means for
      Vec128-class values we must allocated a spill slot number which
      is zero mod 2.

      Similarly, for Vec256 class on amd64, find a spill slot number
      which is zero mod 4.  This guarantees it will be 32 byte
      aligned, which isn't actually necessary on amd64 (we use movUpd
      etc to spill), but seems like good practice.

      Do a rank-based allocation of vregs to spill slot numbers.  We
      put as few values as possible in spill slots, but nevertheless
      need to have a spill slot available for all vregs, just in case.
   */
   /* Int max_ss_no = -1; */

   for (UInt j = 0; j < state->n_vregs; j++) {

      /* True iff this vreg is unused.  In which case we also expect
         that the reg_class field for it has not been set.  */
      if (state->vreg_lrs[j].live_after == INVALID_INSTRNO) {
         vassert(state->vreg_lrs[j].reg_class == HRcINVALID);
         continue;
      }

      /* The spill slots are 64 bits in size.  As per the comment on
         definition of HRegClass in host_generic_regs.h, that means,
         to spill a vreg of class Flt64 or Vec128, we'll need to find
         two adjacent spill slots to use.  For Vec256, we'll need to
         find four adjacent slots to use.  Note, this logic needs to
         kept in sync with the size info on the definition of
         HRegClass. */
      Int ss_no = -1;
      switch (state->vreg_lrs[j].reg_class) {

         case HRcVec128: case HRcFlt64:
            /* Find two adjacent free slots in which between them
               provide up to 128 bits in which to spill the vreg.
               Since we are trying to find an even:odd pair, move
               along in steps of 2 (slots). */
            for (ss_no = 0; ss_no < N_SPILL64S-1; ss_no += 2)
               if (state->ss_busy_until_before[ss_no+0]
                      <= state->vreg_lrs[j].live_after
                   && state->ss_busy_until_before[ss_no+1]
                      <= state->vreg_lrs[j].live_after)
                  break;
            if (ss_no >= N_SPILL64S-1) {
               vpanic("LibVEX_N_SPILL_BYTES is too low.  " 
                      "Increase and recompile.");
            }
            state->ss_busy_until_before[ss_no+0]
               = state->vreg_lrs[j].dead_before;
            state->ss_busy_until_before[ss_no+1]
               = state->vreg_lrs[j].dead_before;
            break;

         default:
            /* The ordinary case -- just find a single spill slot. */
            /* Find the lowest-numbered spill slot which is available
               at the start point of this interval, and assign the
               interval to it. */
            for (ss_no = 0; ss_no < N_SPILL64S; ss_no++)
               if (state->ss_busy_until_before[ss_no]
                   <= state->vreg_lrs[j].live_after)
                  break;
            if (ss_no == N_SPILL64S) {
               vpanic("LibVEX_N_SPILL_BYTES is too low.  " 
                      "Increase and recompile.");
            }
            state->ss_busy_until_before[ss_no] = state->vreg_lrs[j].dead_before;
            break;

      } /* switch (state->vreg_lrs[j].reg_class) */

      /* This reflects LibVEX's hard-wired knowledge of the guest state
         layout: the guest state, then two equal sized areas following
         it for two sets of shadow state, and then the spill area. */
      state->vreg_lrs[j].spill_offset
         = toShort(state->guest_sizeB * 3 + ss_no * 8);

      /* Independent check that we've made a sane choice of slot */
      sanity_check_spill_offset(&state->vreg_lrs[j]);
      /* if (j > max_ss_no) */
      /*    max_ss_no = j; */
   }

   if (0) {
      vex_printf("\n\n");
      for (UInt j = 0; j < state->n_vregs; j++)
         vex_printf("vreg %d    --> spill offset %d\n",
                    j, state->vreg_lrs[j].spill_offset);
   }

   /* --------- Stage 4: establish rreg preferences --------- */

   /* It may be advantageous to allocating certain vregs to specific
      rregs, as a way of avoiding reg-reg moves later.  Here we
      establish which, if any, rreg each vreg would prefer to be in.
      Note that this constrains the allocator -- ideally we end up
      with as few as possible vregs expressing a preference.  

      This is an optimisation: if the .preferred_rreg field is never
      set to anything different from INVALID_HREG, the allocator still
      works. */

   /* 30 Dec 04: removed this mechanism as it does not seem to
      help. */

   /* --------- Stage 5: process instructions --------- */

   /* This is the main loop of the allocator.  First, we need to
      correctly set up our running state, which tracks the status of
      each real register. */

   /* ------ BEGIN: Process each insn in turn. ------ */

   for (UInt ii = 0; ii < instrs_in->insns_used; ii++) {
      HInstr* instr = instrs_in->insns[ii];
      vassert(!state->isIfThenElse(instr));

      if (DEBUG_REGALLOC) {
         vex_printf("\n====----====---- Insn %u ----====----====\n", ii);
         vex_printf("---- ");
         state->ppInstr(instr, state->mode64);
         vex_printf("\n\nInitial state:\n");
         print_state(state);
         vex_printf("\n");
      }

      /* ------------ Sanity checks ------------ */

      /* Sanity checks are expensive.  So they are done only once
         every 17 instructions, and just before the last
         instruction. */
      Bool do_sanity_check
         = toBool(
              False /* Set to True for sanity checking of all insns. */
              || ii == instrs_in->insns_used-1
              || (ii > 0 && (ii % 17) == 0)
           );

      if (do_sanity_check) {

         /* Sanity check 1: all rregs with a hard live range crossing
            this insn must be marked as unavailable in the running
            state. */
         for (UInt j = 0; j < state->rreg_lrs_used; j++) {
            if (state->rreg_lrs_la[j].live_after < ii
                && ii < state->rreg_lrs_la[j].dead_before) {
               /* ii is the middle of a hard live range for some real
                  reg.  Check it's marked as such in the running
                  state. */
               HReg reg = state->rreg_lrs_la[j].rreg;

               if (0) {
                  vex_printf("considering la %d .. db %d   reg = ", 
                             state->rreg_lrs_la[j].live_after, 
                             state->rreg_lrs_la[j].dead_before);
                  state->ppReg(reg);
                  vex_printf("\n");
               }

               /* assert that this rreg is marked as unavailable */
               vassert(!hregIsVirtual(reg));
               vassert(state->rreg_state[hregIndex(reg)].disp == Unavail);
            }
         }

         /* Sanity check 2: conversely, all rregs marked as
            unavailable in the running rreg_state must have a
            corresponding hard live range entry in the rreg_lrs
            array. */
         for (UInt j = 0; j < state->n_rregs; j++) {
            vassert(state->rreg_state[j].disp == Bound
                    || state->rreg_state[j].disp == Free
                    || state->rreg_state[j].disp == Unavail);
            if (state->rreg_state[j].disp != Unavail)
               continue;
            UInt k;
            for (k = 0; k < state->rreg_lrs_used; k++) {
               HReg reg = state->rreg_lrs_la[k].rreg;
               vassert(!hregIsVirtual(reg));
               if (hregIndex(reg) == j
                   && state->rreg_lrs_la[k].live_after < ii 
                   && ii < state->rreg_lrs_la[k].dead_before) 
                  break;
            }
            /* If this vassertion fails, we couldn't find a
               corresponding HLR. */
            vassert(k < state->rreg_lrs_used);
         }

         /* Sanity check 3: all vreg-rreg bindings must bind registers
            of the same class. */
         for (UInt j = 0; j < state->n_rregs; j++) {
            if (state->rreg_state[j].disp != Bound) {
               vassert(state->rreg_state[j].eq_spill_slot == False);
               continue;
            }
            vassert(hregClass(state->univ->regs[j]) 
                    == hregClass(state->rreg_state[j].vreg));
            vassert(hregIsVirtual(state->rreg_state[j].vreg));
         }

         /* Sanity check 4: the vreg_state and rreg_state
            mutually-redundant mappings are consistent.  If
            rreg_state[j].vreg points at some vreg_state entry then
            that vreg_state entry should point back at
            rreg_state[j]. */
         for (UInt j = 0; j < state->n_rregs; j++) {
            if (state->rreg_state[j].disp != Bound)
               continue;
            Int k = hregIndex(state->rreg_state[j].vreg);
            vassert(IS_VALID_VREGNO(k));
            vassert(state->vreg_state[k] == j);
         }
         for (UInt j = 0; j < state->n_vregs; j++) {
            Int k = state->vreg_state[j];
            if (k == INVALID_RREG_NO)
               continue;
            vassert(IS_VALID_RREGNO(k));
            vassert(state->rreg_state[k].disp == Bound);
            vassert(hregIndex(state->rreg_state[k].vreg) == j);
         }

      } /* if (do_sanity_check) */

      /* ------------ end of Sanity checks ------------ */

      /* Do various optimisations pertaining to register coalescing
         and preferencing:
            MOV  v <-> v   coalescing (done here).
            MOV  v <-> r   coalescing (not yet, if ever)
      */
      /* If doing a reg-reg move between two vregs, and the src's live
         range ends here and the dst's live range starts here, bind
         the dst to the src's rreg, and that's all. */
      HReg vregS = INVALID_HREG;
      HReg vregD = INVALID_HREG;
      if (state->isMove(instr, &vregS, &vregD)) {
         if (!hregIsVirtual(vregS)) goto cannot_coalesce;
         if (!hregIsVirtual(vregD)) goto cannot_coalesce;
         /* Check that *isMove is not telling us a bunch of lies ... */
         vassert(hregClass(vregS) == hregClass(vregD));
         Int k = hregIndex(vregS);
         Int m = hregIndex(vregD);
         vassert(IS_VALID_VREGNO(k));
         vassert(IS_VALID_VREGNO(m));
         if (state->vreg_lrs[k].dead_before != ii + 1) goto cannot_coalesce;
         if (state->vreg_lrs[m].live_after != ii) goto cannot_coalesce;
         if (DEBUG_REGALLOC) {
         vex_printf("COALESCE ");
            state->ppReg(vregS);
            vex_printf(" -> ");
            state->ppReg(vregD);
            vex_printf("\n\n");
         }
         /* Find the state entry for vregS. */
         Int n = state->vreg_state[k]; /* k is the index of vregS */
         if (n == INVALID_RREG_NO) {
            /* vregS is not currently in a real register.  So we can't
               do the coalescing.  Give up. */
            goto cannot_coalesce;
         }
         vassert(IS_VALID_RREGNO(n));

         /* Finally, we can do the coalescing.  It's trivial -- merely
            claim vregS's register for vregD. */
         state->rreg_state[n].vreg = vregD;
         vassert(IS_VALID_VREGNO(hregIndex(vregD)));
         vassert(IS_VALID_VREGNO(hregIndex(vregS)));
         state->vreg_state[hregIndex(vregD)] = toShort(n);
         state->vreg_state[hregIndex(vregS)] = INVALID_RREG_NO;

         /* This rreg has become associated with a different vreg and
            hence with a different spill slot.  Play safe. */
         state->rreg_state[n].eq_spill_slot = False;

         /* Move on to the next insn.  We skip the post-insn stuff for
            fixed registers, since this move should not interact with
            them in any way. */
         continue;
      }
     cannot_coalesce:

      /* ------ Free up rregs bound to dead vregs ------ */

      /* Look for vregs whose live range has just ended, and 
	 mark the associated rreg as free. */

      for (UInt j = 0; j < state->n_rregs; j++) {
         if (state->rreg_state[j].disp != Bound)
            continue;
         UInt vregno = hregIndex(state->rreg_state[j].vreg);
         vassert(IS_VALID_VREGNO(vregno));
         if (state->vreg_lrs[vregno].dead_before <= ii) {
            state->rreg_state[j].disp = Free;
            state->rreg_state[j].eq_spill_slot = False;
            Int m = hregIndex(state->rreg_state[j].vreg);
            vassert(IS_VALID_VREGNO(m));
            state->vreg_state[m] = INVALID_RREG_NO;
            if (DEBUG_REGALLOC) {
               vex_printf("free up "); 
               state->ppReg(state->univ->regs[j]); 
               vex_printf("\n");
            }
         }
      }

      /* ------ Pre-instruction actions for fixed rreg uses ------ */

      /* Now we have to deal with rregs which are about to be made
         live by this instruction -- in other words, are entering into
         one of their live ranges.  If any such rreg holds a vreg, we
         will have to free up the rreg.  The simplest solution which
         is correct is to spill the rreg.

         Note we could do better:
         * Could move it into some other free rreg, if one is available 

         Do this efficiently, by incrementally stepping along an array
         of rreg HLRs that are known to be sorted by start point
         (their .live_after field).
      */
      while (True) {
         vassert(state->rreg_lrs_la_next >= 0);
         vassert(state->rreg_lrs_la_next <= state->rreg_lrs_used);
         if (state->rreg_lrs_la_next == state->rreg_lrs_used)
            break; /* no more real reg live ranges to consider */
         if (ii < state->rreg_lrs_la[state->rreg_lrs_la_next].live_after)
            break; /* next live range does not yet start */
         vassert(ii == state->rreg_lrs_la[state->rreg_lrs_la_next].live_after);
         /* rreg_lrs_la[rreg_lrs_la_next].rreg needs to be freed up.
            Find the associated rreg_state entry. */
         /* Note, re ii == state->rreg_lrs_la[rreg_lrs_la_next].live_after.
            Real register live ranges are guaranteed to be well-formed
            in that they start with a write to the register -- Stage 2
            rejects any code not satisfying this.  So the correct
            question to ask is whether
            rreg_lrs_la[rreg_lrs_la_next].live_after == ii, that is,
            whether the reg becomes live after this insn -- rather
            than before it. */
         if (DEBUG_REGALLOC) {
            vex_printf("need to free up rreg: ");
            state->ppReg(state->rreg_lrs_la[state->rreg_lrs_la_next].rreg);
            vex_printf("\n\n");
         }
         Int k = hregIndex(state->rreg_lrs_la[state->rreg_lrs_la_next].rreg);

         /* If this fails, we don't have an entry for this rreg.
            Which we should. */
         vassert(IS_VALID_RREGNO(k));
         Int m = hregIndex(state->rreg_state[k].vreg);
         if (state->rreg_state[k].disp == Bound) {
            /* Yes, there is an associated vreg.  Spill it if it's
               still live. */
            vassert(IS_VALID_VREGNO(m));
            state->vreg_state[m] = INVALID_RREG_NO;
            if (state->vreg_lrs[m].dead_before > ii) {
               vassert(state->vreg_lrs[m].reg_class != HRcINVALID);
               if ((!eq_spill_opt) || !state->rreg_state[k].eq_spill_slot) {
                  HInstr* spill1 = NULL;
                  HInstr* spill2 = NULL;
                  state->genSpill(&spill1, &spill2, state->univ->regs[k],
                                  state->vreg_lrs[m].spill_offset,
                                  state->mode64);
                  vassert(spill1 || spill2); /* can't both be NULL */
                  if (spill1)
                     EMIT_INSTR(spill1);
                  if (spill2)
                     EMIT_INSTR(spill2);
               }
               state->rreg_state[k].eq_spill_slot = True;
            }
         }
         state->rreg_state[k].disp = Unavail;
         state->rreg_state[k].vreg = INVALID_HREG;
         state->rreg_state[k].eq_spill_slot = False;

         /* check for further rregs entering HLRs at this point */
         state->rreg_lrs_la_next++;
      }

      if (DEBUG_REGALLOC) {
         vex_printf("After pre-insn actions for fixed regs:\n");
         print_state(state);
         vex_printf("\n");
      }

      /* ------ Deal with the current instruction. ------ */

      /* Finally we can begin the processing of this instruction
         itself.  The aim is to free up enough rregs for this insn.
         This may generate spill stores since we may have to evict
         some vregs currently in rregs.  Also generates spill loads.
         We also build up the final vreg->rreg mapping to be applied
         to the insn. */

      HRegRemap remap;
      initHRegRemap(&remap);

      /* ------------ BEGIN directReload optimisation ----------- */

      /* If the instruction reads exactly one vreg which is currently
         in a spill slot, and this is last use of that vreg, see if we
         can convert the instruction into one that reads directly from
         the spill slot.  This is clearly only possible for x86 and
         amd64 targets, since ppc and arm are load-store
         architectures.  If successful, replace instrs_in->arr[ii]
         with this new instruction, and recompute its reg usage, so
         that the change is invisible to the standard-case handling
         that follows. */
      
      if (state->directReload != NULL
          && state->reg_usage_arr[ii].n_vRegs <= 2) {
         Bool  debug_direct_reload = False;
         HReg  cand     = INVALID_HREG;
         Bool  nreads   = 0;
         Short spilloff = 0;

         for (UInt j = 0; j < state->reg_usage_arr[ii].n_vRegs; j++) {

            HReg vreg = state->reg_usage_arr[ii].vRegs[j];
            vassert(hregIsVirtual(vreg));

            if (state->reg_usage_arr[ii].vMode[j] == HRmRead) {
               nreads++;
               Int m = hregIndex(vreg);
               vassert(IS_VALID_VREGNO(m));
               Int k = state->vreg_state[m];
               if (!IS_VALID_RREGNO(k)) {
                  /* ok, it is spilled.  Now, is this its last use? */
                  vassert(state->vreg_lrs[m].dead_before >= ii+1);
                  if (state->vreg_lrs[m].dead_before == ii+1
                      && hregIsInvalid(cand)) {
                     spilloff = state->vreg_lrs[m].spill_offset;
                     cand = vreg;
                  }
               }
            }
         }

         if (nreads == 1 && ! hregIsInvalid(cand)) {
            if (state->reg_usage_arr[ii].n_vRegs == 2)
               vassert(! sameHReg(state->reg_usage_arr[ii].vRegs[0],
                                  state->reg_usage_arr[ii].vRegs[1]));

            HInstr* reloaded = state->directReload(instr, cand, spilloff);
            if (debug_direct_reload && reloaded == NULL) {
               vex_printf("[%3d] ", spilloff); ppHReg(cand); vex_printf(" "); 
               state->ppInstr(instr, state->mode64); 
            }
            if (reloaded != NULL) {
               /* Update info about the insn, so it looks as if it had
                  been in this form all along. */
               instr = reloaded;
               instrs_in->insns[ii] = reloaded;
               state->getRegUsage(&state->reg_usage_arr[ii], instr,
                                  state->mode64);
               if (debug_direct_reload && reloaded == NULL) {
                  vex_printf("  -->  ");
                  state->ppInstr(reloaded, state->mode64);
               }
            }

            if (debug_direct_reload && !reloaded)
               vex_printf("\n");
         }

      }

      /* ------------ END directReload optimisation ------------ */

      /* for each virtual reg mentioned in the insn ... */
      for (UInt j = 0; j < state->reg_usage_arr[ii].n_vRegs; j++) {

         HReg vreg = state->reg_usage_arr[ii].vRegs[j];
         vassert(hregIsVirtual(vreg));

         if (0) {
            vex_printf("considering "); state->ppReg(vreg); vex_printf("\n");
         }

         /* Now we're trying to find a rreg for "vreg".  First of all,
            if it already has an rreg assigned, we don't need to do
            anything more.  Inspect the current state to find out. */
         Int m = hregIndex(vreg);
         vassert(IS_VALID_VREGNO(m));
         Short n = state->vreg_state[m];
         if (IS_VALID_RREGNO(n)) {
            vassert(state->rreg_state[n].disp == Bound);
            addToHRegRemap(&remap, vreg, state->univ->regs[n]);
            /* If this rreg is written or modified, mark it as different
               from any spill slot value. */
            if (state->reg_usage_arr[ii].vMode[j] != HRmRead)
               state->rreg_state[n].eq_spill_slot = False;
            continue;
         } else {
            vassert(n == INVALID_RREG_NO);
         }

         /* No luck.  The next thing to do is see if there is a
            currently free rreg available, of the correct class.  If
            so, bag it.  NOTE, we could improve this by selecting an
            rreg for which the next live-range event is as far ahead
            as possible. */
         Int k_suboptimal = -1;
         Int k;
         for (k = 0; k < state->n_rregs; k++) {
            if (state->rreg_state[k].disp != Free
                || hregClass(state->univ->regs[k]) != hregClass(vreg))
               continue;
            if (state->rreg_state[k].has_hlrs) {
               /* Well, at least we can use k_suboptimal if we really
                  have to.  Keep on looking for a better candidate. */
               k_suboptimal = k;
            } else {
               /* Found a preferable reg.  Use it. */
               k_suboptimal = -1;
               break;
            }
         }
         if (k_suboptimal >= 0)
            k = k_suboptimal;

         if (k < state->n_rregs) {
            state->rreg_state[k].disp = Bound;
            state->rreg_state[k].vreg = vreg;
            Int p = hregIndex(vreg);
            vassert(IS_VALID_VREGNO(p));
            state->vreg_state[p] = toShort(k);
            addToHRegRemap(&remap, vreg, state->univ->regs[k]);
            /* Generate a reload if needed.  This only creates needed
               reloads because the live range builder for vregs will
               guarantee that the first event for a vreg is a write.
               Hence, if this reference is not a write, it cannot be
               the first reference for this vreg, and so a reload is
               indeed needed. */
            if (state->reg_usage_arr[ii].vMode[j] != HRmWrite) {
               vassert(state->vreg_lrs[p].reg_class != HRcINVALID);
               HInstr* reload1 = NULL;
               HInstr* reload2 = NULL;
               state->genReload(&reload1, &reload2, state->univ->regs[k],
                                state->vreg_lrs[p].spill_offset, state->mode64);
               vassert(reload1 || reload2); /* can't both be NULL */
               if (reload1)
                  EMIT_INSTR(reload1);
               if (reload2)
                  EMIT_INSTR(reload2);
               /* This rreg is read or modified by the instruction.
                  If it's merely read we can claim it now equals the
                  spill slot, but not so if it is modified. */
               if (state->reg_usage_arr[ii].vMode[j] == HRmRead) {
                  state->rreg_state[k].eq_spill_slot = True;
               } else {
                  vassert(state->reg_usage_arr[ii].vMode[j] == HRmModify);
                  state->rreg_state[k].eq_spill_slot = False;
               }
            } else {
               state->rreg_state[k].eq_spill_slot = False;
            }

            continue;
         }

         /* Well, now we have no option but to spill a vreg.  It's
            important to make a good choice of vreg to spill, and of
            course we need to be careful not to spill a vreg which is
            needed by this insn. */

         /* First, mark in the rreg_state, those rregs which are not spill
            candidates, due to holding a vreg mentioned by this
            instruction.  Or being of the wrong class. */
         for (k = 0; k < state->n_rregs; k++) {
            state->rreg_state[k].is_spill_cand = False;
            if (state->rreg_state[k].disp != Bound)
               continue;
            if (hregClass(state->univ->regs[k]) != hregClass(vreg))
               continue;
            state->rreg_state[k].is_spill_cand = True;
            /* Note, the following loop visits only the virtual regs
               mentioned by the instruction. */
            for (m = 0; m < state->reg_usage_arr[ii].n_vRegs; m++) {
               if (sameHReg(state->rreg_state[k].vreg,
                            state->reg_usage_arr[ii].vRegs[m])) {
                  state->rreg_state[k].is_spill_cand = False;
                  break;
               }
            }
         }

         /* We can choose to spill any rreg satisfying
            rreg_state[r].is_spill_cand (so to speak).  Choose r so that
            the next use of its associated vreg is as far ahead as
            possible, in the hope that this will minimise the number
            of consequent reloads required. */
         Int spillee
            = findMostDistantlyMentionedVReg ( 
                 state->reg_usage_arr, ii+1, instrs_in->insns_used,
                 state->rreg_state, state->n_rregs);

         if (spillee == -1) {
            /* Hmmmmm.  There don't appear to be any spill candidates.
               We're hosed. */
            vex_printf("reg_alloc: can't find a register in class: ");
            ppHRegClass(hregClass(vreg));
            vex_printf("\n");
            vpanic("reg_alloc: can't create a free register.");
         }

         /* Right.  So we're going to spill rreg_state[spillee]. */
         vassert(IS_VALID_RREGNO(spillee));
         vassert(state->rreg_state[spillee].disp == Bound);
         /* check it's the right class */
         vassert(hregClass(state->univ->regs[spillee]) == hregClass(vreg));
         /* check we're not ejecting the vreg for which we are trying
            to free up a register. */
         vassert(! sameHReg(state->rreg_state[spillee].vreg, vreg));

         m = hregIndex(state->rreg_state[spillee].vreg);
         vassert(IS_VALID_VREGNO(m));

         /* So here's the spill store.  Assert that we're spilling a
            live vreg. */
         vassert(state->vreg_lrs[m].dead_before > ii);
         vassert(state->vreg_lrs[m].reg_class != HRcINVALID);
         if ((!eq_spill_opt) || !state->rreg_state[spillee].eq_spill_slot) {
            HInstr* spill1 = NULL;
            HInstr* spill2 = NULL;
            state->genSpill(&spill1, &spill2, state->univ->regs[spillee],
                            state->vreg_lrs[m].spill_offset, state->mode64);
            vassert(spill1 || spill2); /* can't both be NULL */
            if (spill1)
               EMIT_INSTR(spill1);
            if (spill2)
               EMIT_INSTR(spill2);
         }

         /* Update the rreg_state to reflect the new assignment for this
            rreg. */
         state->rreg_state[spillee].vreg = vreg;
         state->vreg_state[m] = INVALID_RREG_NO;

         state->rreg_state[spillee].eq_spill_slot = False; /* be safe */

         m = hregIndex(vreg);
         vassert(IS_VALID_VREGNO(m));
         state->vreg_state[m] = toShort(spillee);

         /* Now, if this vreg is being read or modified (as opposed to
            written), we have to generate a reload for it. */
         if (state->reg_usage_arr[ii].vMode[j] != HRmWrite) {
            vassert(state->vreg_lrs[m].reg_class != HRcINVALID);
            HInstr* reload1 = NULL;
            HInstr* reload2 = NULL;
            state->genReload(&reload1, &reload2, state->univ->regs[spillee],
                             state->vreg_lrs[m].spill_offset, state->mode64);
            vassert(reload1 || reload2); /* can't both be NULL */
            if (reload1)
               EMIT_INSTR(reload1);
            if (reload2)
               EMIT_INSTR(reload2);
            /* This rreg is read or modified by the instruction.
               If it's merely read we can claim it now equals the
               spill slot, but not so if it is modified. */
            if (state->reg_usage_arr[ii].vMode[j] == HRmRead) {
               state->rreg_state[spillee].eq_spill_slot = True;
            } else {
               vassert(state->reg_usage_arr[ii].vMode[j] == HRmModify);
               state->rreg_state[spillee].eq_spill_slot = False;
            }
         }

         /* So after much twisting and turning, we have vreg mapped to
            rreg_state[spillee].rreg.  Note that in the map. */
         addToHRegRemap(&remap, vreg, state->univ->regs[spillee]);

      } /* iterate over virtual registers in this instruction. */

      /* We've finished clowning around with registers in this instruction.
         Three results:
         - the running rreg_state[] has been updated
         - a suitable vreg->rreg mapping for this instruction has been 
           constructed
         - spill and reload instructions may have been emitted.

        The final step is to apply the mapping to the instruction, 
        and emit that.
      */

      /* NOTE, DESTRUCTIVELY MODIFIES instrs_in->arr[ii]. */
      state->mapRegs(&remap, instrs_in->insns[ii], state->mode64);
      EMIT_INSTR(instrs_in->insns[ii]);

      if (DEBUG_REGALLOC) {
         vex_printf("After dealing with current insn:\n");
         print_state(state);
         vex_printf("\n");
      }

      /* ------ Post-instruction actions for fixed rreg uses ------ */

      /* Now we need to check for rregs exiting fixed live ranges
         after this instruction, and if so mark them as free. */
      while (True) {
         vassert(state->rreg_lrs_db_next >= 0);
         vassert(state->rreg_lrs_db_next <= state->rreg_lrs_used);
         if (state->rreg_lrs_db_next == state->rreg_lrs_used)
            break; /* no more real reg live ranges to consider */
         if (ii+1 < state->rreg_lrs_db[state->rreg_lrs_db_next].dead_before)
            break; /* next live range does not yet start */
         vassert(ii+1 == state->rreg_lrs_db[state->rreg_lrs_db_next].dead_before);
         /* rreg_lrs_db[[rreg_lrs_db_next].rreg is exiting a hard live
            range.  Mark it as such in the main rreg_state array. */
         HReg reg = state->rreg_lrs_db[state->rreg_lrs_db_next].rreg;
         vassert(!hregIsVirtual(reg));
         Int k = hregIndex(reg);
         vassert(IS_VALID_RREGNO(k));
         vassert(state->rreg_state[k].disp == Unavail);
         state->rreg_state[k].disp = Free;
         state->rreg_state[k].vreg = INVALID_HREG;
         state->rreg_state[k].eq_spill_slot = False;

         /* check for further rregs leaving HLRs at this point */
         state->rreg_lrs_db_next++;
      }

      if (DEBUG_REGALLOC) {
         vex_printf("After post-insn actions for fixed regs:\n");
         print_state(state);
         vex_printf("\n");
      }

   } /* iterate over insns */

   /* ------ END: Process each insn in turn. ------ */

   /* free(state->rreg_state); */
   /* free(state->rreg_lrs); */
   /* if (state->vreg_lrs) free(state->vreg_lrs); */

   /* Paranoia */
   vassert(state->rreg_lrs_la_next == state->rreg_lrs_used);
   vassert(state->rreg_lrs_db_next == state->rreg_lrs_used);

   return instrs_out;

#  undef INVALID_INSTRNO
#  undef EMIT_INSTR
}


/* A target-independent register allocator.  Requires various
   functions which it uses to deal abstractly with instructions and
   registers, since it cannot have any target-specific knowledge.

   Returns a new block of instructions, which, as a result of the
   behaviour of mapRegs, will be in-place modifications of the
   original instructions.

   Requires that the incoming code has been generated using
   vreg numbers 0, 1 .. n_vregs-1.  Appearance of a vreg outside
   that range is a checked run-time error.

   Takes a block of unallocated insns. Returns a block of allocated insns.
   Both blocks have the same structure, including any HInstrIfThenElse.
*/
HInstrSB* doRegisterAllocation (

   /* Incoming virtual-registerised code. */ 
   HInstrSB* sb_in,

   /* The real-register universe to use.  This contains facts about
      real registers, one of which is the set of registers available
      for allocation. */
   const RRegUniverse* univ,

   /* Return True iff the given insn is a reg-reg move, in which
      case also return the src and dst regs. */
   Bool (*isMove) ( const HInstr*, HReg*, HReg* ),

   /* Get info about register usage in this insn. */
   void (*getRegUsage) ( HRegUsage*, const HInstr*, Bool ),

   /* Apply a reg-reg mapping to an insn. */
   void (*mapRegs) ( HRegRemap*, HInstr*, Bool ),

   /* Is this instruction actually HInstrIfThenElse? */
   HInstrIfThenElse* (*isIfThenElse) (const HInstr*),

   /* Return one, or, if we're unlucky, two insn(s) to spill/restore a
      real reg to a spill slot byte offset.  The two leading HInstr**
      args are out parameters, through which the generated insns are
      returned.  Also (optionally) a 'directReload' function, which
      attempts to replace a given instruction by one which reads
      directly from a specified spill slot.  May be NULL, in which
      case the optimisation is not attempted. */
   void    (*genSpill)  ( HInstr**, HInstr**, HReg, Int, Bool ),
   void    (*genReload) ( HInstr**, HInstr**, HReg, Int, Bool ),
   HInstr* (*directReload) ( HInstr*, HReg, Short ),
   Int     guest_sizeB,

   /* For debug printing only. */
   void (*ppInstr) ( const HInstr*, Bool ),
   void (*ppReg) ( HReg ),

   /* 32/64bit mode */
   Bool mode64
)
{
   /* The output array of instructions. */
   HInstrSB* sb_out = newHInstrSB();

   vassert(0 == (guest_sizeB % LibVEX_GUEST_STATE_ALIGN));
   STATIC_ASSERT(0 == (LibVEX_N_SPILL_BYTES % LibVEX_GUEST_STATE_ALIGN));

   RegAllocState state;
   initRegAllocState(&state, univ, isMove, getRegUsage, mapRegs, isIfThenElse,
                     genSpill, genReload, directReload, guest_sizeB, ppInstr,
                     ppReg, mode64, sb_in->insns, sb_in->n_vregs);
   sb_out->insns = regAlloc_HInstrVec(&state, sb_in->insns);
   return sb_out;
}



/*---------------------------------------------------------------*/
/*---                                       host_reg_alloc2.c ---*/
/*---------------------------------------------------------------*/
