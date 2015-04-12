
/*---------------------------------------------------------------*/
/*--- begin                               host_generic_regs.c ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2004-2013 OpenWorks LLP
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


/*---------------------------------------------------------*/
/*--- Representing HOST REGISTERS                       ---*/
/*---------------------------------------------------------*/

void ppHRegClass ( HRegClass hrc )
{
   switch (hrc) {
      case HRcInt32:   vex_printf("HRcInt32"); break;
      case HRcInt64:   vex_printf("HRcInt64"); break;
      case HRcFlt32:   vex_printf("HRcFlt32"); break;
      case HRcFlt64:   vex_printf("HRcFlt64"); break;
      case HRcVec64:   vex_printf("HRcVec64"); break;
      case HRcVec128:  vex_printf("HRcVec128"); break;
      default: vpanic("ppHRegClass");
   }
}

/* Generic printing for registers. */
void ppHReg ( HReg r ) 
{
   if (hregIsInvalid(r)) {
      vex_printf("HReg_INVALID");
      return;
   }
   const Bool   isV     = hregIsVirtual(r);
   const HChar* maybe_v = isV ? "v" : "";
   const UInt   regNN   = isV ? hregIndex(r) : hregEncoding(r);
   /* For real registers, we show the encoding.  But the encoding is
      always zero for virtual registers, so that's pointless -- hence
      show the index number instead. */
   switch (hregClass(r)) {
      case HRcInt32:   vex_printf("%%%sr%u", maybe_v, regNN); return;
      case HRcInt64:   vex_printf("%%%sR%u", maybe_v, regNN); return;
      case HRcFlt32:   vex_printf("%%%sF%u", maybe_v, regNN); return;
      case HRcFlt64:   vex_printf("%%%sD%u", maybe_v, regNN); return;
      case HRcVec64:   vex_printf("%%%sv%u", maybe_v, regNN); return;
      case HRcVec128:  vex_printf("%%%sV%u", maybe_v, regNN); return;
      default: vpanic("ppHReg");
   }
}


/*---------------------------------------------------------*/
/*--- Real register Universes.                          ---*/
/*---------------------------------------------------------*/

void RRegUniverse__init ( /*OUT*/RRegUniverse* univ )
{
   *univ = (RRegUniverse){};
   univ->size      = 0;
   univ->allocable = 0;
   for (UInt i = 0; i < N_RREGUNIVERSE_REGS; i++) {
      univ->regs[i] = HReg_INVALID;
   }
}

void RRegUniverse__check_is_sane ( const RRegUniverse* univ )
{
   /* Check Real-Register-Universe invariants.  All of these are
      important. */
   vassert(univ->size > 0);
   vassert(univ->size <= N_RREGUNIVERSE_REGS);
   vassert(univ->allocable <= univ->size);
   for (UInt i = 0; i < univ->size; i++) {
      HReg reg = univ->regs[i];
      vassert(!hregIsInvalid(reg));
      vassert(!hregIsVirtual(reg));
      vassert(hregIndex(reg) == i);
   }
   for (UInt i = univ->size; i < N_RREGUNIVERSE_REGS; i++) {
      HReg reg = univ->regs[i];
      vassert(hregIsInvalid(reg));
   }
}


/*---------------------------------------------------------*/
/*--- Real register sets                                ---*/
/*---------------------------------------------------------*/

STATIC_ASSERT(N_RREGUNIVERSE_REGS <= 8 * sizeof(ULong));

/* Print a register set, using the arch-specific register printing
   function |regPrinter| supplied. */
void RRegSet__pp ( const RRegSet* set, void (*regPrinter)(HReg) )
{
   const RRegUniverse* univ = set->univ;
   Bool first = True;
   vex_printf("{");
   for (UInt i = 0; i < 8 * sizeof(ULong); i++) {
      if (0ULL == (set->bits & (1ULL << i)))
         continue;
      vassert(i < univ->size);
      if (!first) {
         vex_printf(",");
      } else {
         first = False;
      }
      regPrinter(univ->regs[i]);
   }
   vex_printf("}");
}

/* Initialise an RRegSet, making it empty. */
inline void RRegSet__init ( /*OUT*/RRegSet* set, const RRegUniverse* univ )
{
   set->bits = 0;
   set->univ = univ;
}

/* Create a new, empty, set, in the normal (transient) heap. */
RRegSet* RRegSet__new ( const RRegUniverse* univ )
{
   vassert(univ);
   RRegSet* set = LibVEX_Alloc_inline(sizeof(RRegSet));
   RRegSet__init(set, univ);
   return set;
}

/* Return the RRegUniverse for a given RRegSet. */
const RRegUniverse* RRegSet__getUniverse ( const RRegSet* set )
{
   return set->univ;
}

/* Install elements from vec[0 .. nVec-1].  The previous contents of
   |dst| are lost.  vec[0 .. nVec-1] may not contain any
   duplicates. */
void RRegSet__fromVec ( /*MOD*/RRegSet* dst, const HReg* vec, UInt nVec )
{
   dst->bits = 0;
   for (UInt i = 0; i < nVec; i++) {
      HReg r = vec[i];
      vassert(!hregIsInvalid(r) && !hregIsVirtual(r));
      UInt ix = hregIndex(r);
      vassert(ix < dst->univ->size);
      dst->bits |= (1ULL << ix);
   }
}

/* Copy the contents of |regs| into |dst|.  The previous contents of
   |dst| are lost. */
void RRegSet__copy ( /*MOD*/RRegSet* dst, const RRegSet* regs )
{
   vassert(dst->univ == regs->univ);
   dst->bits = regs->bits;
}

/* Add |reg| to |dst|. */
void RRegSet__add ( /*MOD*/RRegSet* dst, HReg reg )
{
   vassert(!hregIsInvalid(reg) && !hregIsVirtual(reg));
   UInt ix = hregIndex(reg);
   vassert(ix < dst->univ->size);
   dst->bits |= (1ULL << ix);
}

/* Remove |reg| from |dst|. */
void RRegSet__del ( /*MOD*/RRegSet* dst, HReg reg )
{
   vassert(!hregIsInvalid(reg) && !hregIsVirtual(reg));
   UInt ix = hregIndex(reg);
   vassert(ix < dst->univ->size);
   dst->bits &= ~(1ULL << ix);
}

/* Add |regs| to |dst|. */
void RRegSet__plus ( /*MOD*/RRegSet* dst, const RRegSet* regs )
{
   vassert(dst->univ == regs->univ);
   dst->bits |= regs->bits;
}

/* Remove |regs| from |dst|. */
void RRegSet__minus ( /*MOD*/RRegSet* dst, const RRegSet* regs )
{
   vassert(dst->univ == regs->univ);
   dst->bits &= (~regs->bits);
}

/* Returns the number of elements in |set|. */
UInt RRegSet__card ( const RRegSet* set )
{
   return __builtin_popcountll(set->bits);
}

/* Remove non-allocatable registers from this set.  Because the set
   carries its register universe, we can consult that to find the
   non-allocatable registers, so no other parameters are needed. */
void RRegSet__deleteNonAllocatable ( /*MOD*/RRegSet* set )
{
   const RRegUniverse* univ = set->univ;
   UInt allocable = univ->allocable;
   if (UNLIKELY(allocable == N_RREGUNIVERSE_REGS)) {
      return;
      /* otherwise we'd get an out-of-range shift below */
   }
   vassert(allocable > 0 && allocable < N_RREGUNIVERSE_REGS);
   ULong mask = (1ULL << allocable) - 1;
   set->bits &= mask;
}


struct _RRegSetIterator {
   const RRegSet* set;
   UInt           nextIx;  /* The next |set->bits| index to try */
};

/* Create a new iterator.  It can't be used until it is first __init'd. */
RRegSetIterator* RRegSetIterator__new ( void )
{
   RRegSetIterator* iter = LibVEX_Alloc_inline(sizeof(RRegSetIterator));
   vex_bzero(iter, sizeof(*iter));
   return iter;
}

/* Initialise an iterator. */
void RRegSetIterator__init ( /*OUT*/RRegSetIterator* iter,
                             const RRegSet* set )
{
   iter->set    = set;
   iter->nextIx = 0;
   /* We're going to iterate only up as far as the Universe size, so
      check that there are no elements above that.  RRegSet__add and
      __fromVec should ensure that is never the case, and there are no
      other ways to add elements to a set. */
   const RRegUniverse* univ = set->univ;
   if (LIKELY(univ->size < 64)) {
      vassert((set->bits >> univ->size) == 0);
   } else {
      vassert(univ->size == 64);
   }
}

/* Get the next element from the set, or HReg_INVALID if there is
   none. */
HReg RRegSetIterator__next ( /*MOD*/RRegSetIterator* iter )
{
   const RRegSet* set = iter->set;
   /* If this fails, it's possibly a sign that the __init call for
      |iter| was missed. */
   vassert(iter->set);

   const RRegUniverse* univ  = set->univ;
   const UInt          maxIx = univ->size;
   vassert(iter->nextIx <= maxIx);
   while (1) {
      if (UNLIKELY(iter->nextIx >= maxIx)) {
         return HReg_INVALID;
      }
      if (UNLIKELY(0ULL != (set->bits & (1ULL << iter->nextIx)))) {
         return univ->regs[iter->nextIx++];
      }
      iter->nextIx++;
   }
   /*NOTREACHED*/
}


/*---------------------------------------------------------*/
/*--- Helpers for recording reg usage (for reg-alloc)   ---*/
/*---------------------------------------------------------*/

void ppHRegUsage ( const RRegUniverse* univ, HRegUsage* tab )
{
   /* This is going to fail miserably if N_RREGUNIVERSE_REGS exceeds
      64.  So let's cause it to fail in an obvious way. */
   vassert(N_RREGUNIVERSE_REGS == 64);

   vex_printf("HRegUsage {\n");
   /* First print the real regs */
   for (UInt i = 0; i < N_RREGUNIVERSE_REGS; i++) {
      Bool rRd = (tab->rRead    & (1ULL << i)) != 0;
      Bool rWr = (tab->rWritten & (1ULL << i)) != 0;
      const HChar* str = "Modify ";
      /**/ if (!rRd && !rWr) { continue; }
      else if ( rRd && !rWr) { str = "Read   "; }
      else if (!rRd &&  rWr) { str = "Write  "; }
      /* else "Modify" is correct */
      vex_printf("   %s ", str);
      ppHReg(univ->regs[i]);
      vex_printf("\n");
   }
   /* and now the virtual registers */
   for (UInt i = 0; i < tab->n_vRegs; i++) {
      const HChar* str = NULL;
      switch (tab->vMode[i]) {
         case HRmRead:   str = "Read   "; break;
         case HRmWrite:  str = "Write  "; break;
         case HRmModify: str = "Modify "; break;
         default: vpanic("ppHRegUsage");
      }
      vex_printf("   %s ", str);
      ppHReg(tab->vRegs[i]);
      vex_printf("\n");
   }
   vex_printf("}\n");
}


/* Add a register to a usage table.  Combines incoming read uses with
   existing write uses into a modify use, and vice versa.  Does not
   create duplicate entries -- each reg is only mentioned once.  
*/
void addHRegUse ( HRegUsage* tab, HRegMode mode, HReg reg )
{
   /* Because real and virtual registers are represented differently,
      they have completely different paths here. */
   if (LIKELY(hregIsVirtual(reg))) {
      /* Virtual register */
      UInt i;
      /* Find it ... */
      for (i = 0; i < tab->n_vRegs; i++)
         if (sameHReg(tab->vRegs[i], reg))
            break;
      if (i == tab->n_vRegs) {
         /* Not found, add new entry. */
         vassert(tab->n_vRegs < N_HREGUSAGE_VREGS);
         tab->vRegs[tab->n_vRegs] = reg;
         tab->vMode[tab->n_vRegs] = mode;
         tab->n_vRegs++;
      } else {
         /* Found: combine or ignore. */
         /* This is a greatest-lower-bound operation in the poset:

               R   W
                \ /
                 M

            Need to do: tab->mode[i] = GLB(tab->mode, mode).  In this
            case very simple -- if tab->mode[i] != mode then result must
            be M.
         */
         if (tab->vMode[i] == mode) {
            /* duplicate, ignore */
         } else {
            tab->vMode[i] = HRmModify;
         }
      }
   } else {
      /* Real register */
      UInt ix = hregIndex(reg);
      vassert(ix < N_RREGUNIVERSE_REGS);
      ULong mask = 1ULL << ix;
      switch (mode) {
         case HRmRead:   tab->rRead |= mask; break;
         case HRmWrite:  tab->rWritten |= mask; break;
         case HRmModify: tab->rRead |= mask; tab->rWritten |= mask; break;
         default: vassert(0);
      }
   }
}

Bool HRegUsage__contains ( const HRegUsage* tab, HReg reg )
{
   vassert(!hregIsInvalid(reg));
   if (hregIsVirtual(reg)) {
      for (UInt i = 0; i < tab->n_vRegs; i++) {
         if (sameHReg(reg, tab->vRegs[i]))
            return True;
      }
      return False;
   } else {
      UInt ix = hregIndex(reg);
      vassert(ix < N_RREGUNIVERSE_REGS);
      ULong mentioned = tab->rRead | tab->rWritten;
      return (mentioned & (1ULL << ix)) != 0;
   }
   /*NOTREACHED*/
}

void addHRegUse_from_RRegSet ( HRegUsage* tab,
                               HRegMode mode, const RRegSet* set )
{
   STATIC_ASSERT(sizeof(tab->rRead) == sizeof(tab->rWritten));
   STATIC_ASSERT(sizeof(tab->rRead) == sizeof(set->bits));
   switch (mode) {
      case HRmRead:   tab->rRead    |= set->bits; break;
      case HRmWrite:  tab->rWritten |= set->bits; break;
      case HRmModify: tab->rRead    |= set->bits;
                      tab->rWritten |= set->bits; break;
      default: vassert(0);
   }
}


/*---------------------------------------------------------*/
/*--- Indicating register remappings (for reg-alloc)    ---*/
/*---------------------------------------------------------*/

void ppHRegRemap ( HRegRemap* map )
{
   Int   i;
   vex_printf("HRegRemap {\n");
   for (i = 0; i < map->n_used; i++) {
      vex_printf("   ");
      ppHReg(map->orig[i]);
      vex_printf("  -->  ");
      ppHReg(map->replacement[i]);
      vex_printf("\n");
   }
   vex_printf("}\n");
}


void addToHRegRemap ( HRegRemap* map, HReg orig, HReg replacement )
{
   Int i;
   for (i = 0; i < map->n_used; i++)
      if (sameHReg(map->orig[i], orig))
         vpanic("addToHRegMap: duplicate entry");
   if (!hregIsVirtual(orig))
      vpanic("addToHRegMap: orig is not a vreg");
   if (hregIsVirtual(replacement))
      vpanic("addToHRegMap: replacement is a vreg");

   vassert(map->n_used+1 < N_HREG_REMAP);
   map->orig[map->n_used]        = orig;
   map->replacement[map->n_used] = replacement;
   map->n_used++;
}


HReg lookupHRegRemap ( HRegRemap* map, HReg orig )
{
   Int i;
   if (!hregIsVirtual(orig))
      return orig;
   for (i = 0; i < map->n_used; i++)
      if (sameHReg(map->orig[i], orig))
         return map->replacement[i];
   vpanic("lookupHRegRemap: not found");
}


/*---------------------------------------------------------*/
/*--- Abstract instructions                             ---*/
/*---------------------------------------------------------*/

HInstrArray* newHInstrArray ( void )
{
   HInstrArray* ha = LibVEX_Alloc_inline(sizeof(HInstrArray));
   ha->arr_size = 4;
   ha->arr_used = 0;
   ha->arr      = LibVEX_Alloc_inline(ha->arr_size * sizeof(HInstr*));
   ha->n_vregs  = 0;
   return ha;
}

__attribute__((noinline))
void addHInstr_SLOW ( HInstrArray* ha, HInstr* instr )
{
   vassert(ha->arr_used == ha->arr_size);
   Int      i;
   HInstr** arr2 = LibVEX_Alloc_inline(ha->arr_size * 2 * sizeof(HInstr*));
   for (i = 0; i < ha->arr_size; i++) {
      arr2[i] = ha->arr[i];
   }
   ha->arr_size *= 2;
   ha->arr = arr2;
   addHInstr(ha, instr);
}


/*---------------------------------------------------------*/
/*--- C-Call return-location actions                    ---*/
/*---------------------------------------------------------*/

void ppRetLoc ( RetLoc ska )
{
   switch (ska.pri) {
      case RLPri_INVALID:
         vex_printf("RLPri_INVALID"); return;
      case RLPri_None:
         vex_printf("RLPri_None");    return;
      case RLPri_Int:
         vex_printf("RLPri_Int");     return;
      case RLPri_2Int:
         vex_printf("RLPri_2Int");    return;
      case RLPri_V128SpRel:
         vex_printf("RLPri_V128SpRel(%d)", ska.spOff); return;
      case RLPri_V256SpRel:
         vex_printf("RLPri_V256SpRel(%d)", ska.spOff); return;
      default:
         vpanic("ppRetLoc");
   }
}


/*---------------------------------------------------------*/
/*--- Helpers for Relocations                           ---*/
/*---------------------------------------------------------*/

static void ppRelocWhere ( RelocWhere rlw )
{
   ppNLabelZone(rlw.zone);
   vex_printf("[%u]", rlw.offset);
}

static void ppRelocDst ( RelocDst rdst )
{
   if (rdst.isOffset) {
      ppRelocWhere( mkRelocWhere(rdst.zone, rdst.num) );
   } else {
      ppNLabel( mkNLabel(rdst.zone, rdst.num) );
   }
}

void ppRelocation ( Relocation* rl )
{
   vex_printf("(");
   ppRelocWhere(rl->where);
   vex_printf(" bits[%u..%u]) refers-to (", rl->bitNoMax, rl->bitNoMin);
   ppRelocDst(rl->dst);
   vex_printf(") bias %d rshift %u", rl->bias, (UInt)rl->rshift);
}


/*---------------------------------------------------------*/
/*--- NCode generation helpers                          ---*/
/*---------------------------------------------------------*/

/* Find the length of a vector of HRegs that is terminated by
   an HReg_INVALID. */
UInt hregVecLen ( const HReg* vec )
{
   UInt i;
   for (i = 0; !hregIsInvalid(vec[i]); i++)
      ;
   return i;
}


/* Find the real (hard) register for |r| by looking up in |map|. */
HReg mapNReg ( const NRegMap* map, NReg r )
{
   UInt limit = 0;
   const HReg* arr = NULL;
   switch (r.role) {
      case Nrr_Result:   limit = map->nRegsR; arr = map->regsR; break;
      case Nrr_Argument: limit = map->nRegsA; arr = map->regsA; break;
      case Nrr_Scratch:  limit = map->nRegsS; arr = map->regsS; break;
      default: vpanic("mapNReg: invalid reg role");
   }
   vassert(r.num < limit);
   return arr[r.num];
}


/* Compute the minimal set of registers to preserve around calls
   embedded within NCode blocks. */
void calcRegistersToPreserveAroundNCodeCall (
        /*OUT*/RRegSet* result,
        const RRegSet*  hregsLiveAfterTheNCodeBlock,
        const RRegSet*  abiCallerSavedRegs,
        const NRegMap*  nregMap,
        NReg nregResHi,
        NReg nregResLo
     )
{
   /* This function deals with one of the main difficulties of NCode
      templates, which is that of figuring out the minimal set of
      registers to save across calls embedded inside NCode blocks.  As
      far as I can see, the set is:

      (1)   registers live after the NCode block  
      (2)   + the Arg, Res and Scratch registers for the block
      (3)   - Abi_Callee_Saved registers
      (4)   - the Arg/Res/Scratch register(s) into which the call
              will place its results
  
      (1) because that's the set of regs that reg-alloc expects to
          not be trashed by the NCode block
      (2) because Arg/Res/Scratch regs can be used freely within the
          NCode block, so we have to keep them alive
      (3) because preserving Callee saved regs is obviously pointless
      (4) because preserving the call's result reg(s) will result in
          the restore sequence overwriting the result of the call

      (2) (3) (4) are either constants or something we can find from
      inspection of the relevant NInstr (call) alone.  (1) is
      something that depends on instructions after the NCode block
      and so is something that the register allocator has to tell us.

      Another detail is that we remove from the set, all registers not
      available to the register allocator.  That is, we save across
      the call, only registers available to the allocator.  That
      assumes that all fixed-use or otherwise-not-allocatable
      registers, that we care about, are callee-saved.  AFAIK the only
      important register is the baseblock register, and that is indeed
      callee-saved on all targets.
   */
   const RRegUniverse* univ 
      = RRegSet__getUniverse(hregsLiveAfterTheNCodeBlock);

   const RRegSet* set_1 = hregsLiveAfterTheNCodeBlock;

   RRegSet set_2;
   RRegSet__init(&set_2, univ);
   for (UInt i = 0; i < nregMap->nRegsR; i++)
      RRegSet__add(&set_2, nregMap->regsR[i]);
   for (UInt i = 0; i < nregMap->nRegsA; i++)
      RRegSet__add(&set_2, nregMap->regsA[i]);
   for (UInt i = 0; i < nregMap->nRegsS; i++)
      RRegSet__add(&set_2, nregMap->regsS[i]);

   const RRegSet* set_3 = abiCallerSavedRegs;
   vassert(univ == RRegSet__getUniverse(set_3));

   RRegSet set_4;
   RRegSet__init(&set_4, univ);
   if (!isNRegINVALID(nregResHi))
      RRegSet__add(&set_4, mapNReg(nregMap, nregResHi));
   if (!isNRegINVALID(nregResLo))
      RRegSet__add(&set_4, mapNReg(nregMap, nregResLo));

   RRegSet__init(result, univ);
   RRegSet__copy(result, set_1);
   RRegSet__plus(result, &set_2);
   RRegSet__minus(result, set_3);
   RRegSet__minus(result, &set_4);

   if (0) {
      vex_printf("              # set1: ");
      RRegSet__pp(set_1, ppHReg); vex_printf("\n");
      vex_printf("              # set2: ");
      RRegSet__pp(&set_2, ppHReg); vex_printf("\n");
      vex_printf("              # set3: ");
      RRegSet__pp(set_3, ppHReg); vex_printf("\n");
      vex_printf("              # set4: ");
      RRegSet__pp(&set_4, ppHReg); vex_printf("\n");
      vex_printf("              # pres: ");
      RRegSet__pp(result, ppHReg); vex_printf("\n");
   }

   /* Remove any non allocatable registers (see big comment above) */
   RRegSet__deleteNonAllocatable(result);
}


/*---------------------------------------------------------------*/
/*--- end                                 host_generic_regs.c ---*/
/*---------------------------------------------------------------*/
