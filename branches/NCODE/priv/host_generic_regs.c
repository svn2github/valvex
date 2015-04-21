
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
void ppHRegGENERIC ( HReg r ) 
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
      ppHRegGENERIC(univ->regs[i]);
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
      ppHRegGENERIC(tab->vRegs[i]);
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

void ppHRegRemap ( const HRegRemap* map )
{
   Int   i;
   vex_printf("HRegRemap {\n");
   for (i = 0; i < map->n_used; i++) {
      vex_printf("   ");
      ppHRegGENERIC(map->orig[i]);
      vex_printf("  -->  ");
      ppHRegGENERIC(map->replacement[i]);
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


HReg lookupHRegRemap ( const HRegRemap* map, HReg orig )
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


/* Find the length of a vector of NRegs that is terminated by
   an NReg_INVALID. */
UInt nregVecLen ( const NReg* vec )
{
   UInt i;
   for (i = 0; !isNRegINVALID(vec[i]); i++)
      ;
   return i;
}


/* Find the length of a vector of NInstr*s that is terminated by
   NULL. */
UInt ninstrVecLen ( NInstr** const vec )
{
   UInt i;
   for (i = 0; vec[i]; i++)
      ;
   return i;
}


/* Print a HInstrNCode.  Caller must supply a register-printing
   routine and a bit of text identifying the host architecture. */
void HInstrNCode__show ( const HInstrNCode* details,
                         void (*ppHReg)(HReg), const HChar* hostName )
{
   NCodeTemplate* tmpl = details->tmpl;
   vex_printf("NCode-%s:%s [", hostName, tmpl->name);
   UInt j;
   for (j = 0; j < tmpl->nres; j++) {
      ppHReg(details->regsR[j]);
      if (j != tmpl->nres-1) vex_printf(" ");
   }
   vex_printf("] <= [");
   for (j = 0; j < tmpl->narg; j++) {
      ppHReg(details->regsA[j]);
      if (j != tmpl->narg-1) vex_printf(" ");
   }
   vex_printf("] scratch [");
   for (j = 0; j < tmpl->nscr; j++) {
      ppHReg(details->regsS[j]);
      if (j != tmpl->nscr-1) vex_printf(" ");
   }
   vex_printf("]");
}


/* Update |u| with the register usages of |details|. */
void HInstrNCode__getRegUsage ( /*MOD*/HRegUsage* u,
                                const HInstrNCode* details )
{
   NCodeTemplate* tmpl = details->tmpl;
   // It writes the result and scratch registers.
   UInt j;
   for (j = 0; j < tmpl->nres; j++)
      addHRegUse(u, HRmWrite, details->regsR[j]);
   for (j = 0; j < tmpl->nscr; j++)
      addHRegUse(u, HRmWrite, details->regsS[j]);
   // It both reads and writes the arg regs.  We have to say
   // they are written in order to force them to be allocated
   // different registers from the arg and scratch registers,
   // since we have no way to ensure that the NCode block
   // doesn't write its scratch and result registers and later
   // on read the argument registers.
   for (j = 0; j < tmpl->narg; j++)
      addHRegUse(u, HRmModify, details->regsA[j]);
}


/* Apply |map| to the registers in |details|. */
void HInstrNCode__mapRegs ( /*MOD*/HInstrNCode* details,
                            const HRegRemap* map )
{
   NCodeTemplate*   tmpl    = details->tmpl;
   UInt j;
   for (j = 0; j < tmpl->nres; j++)
      details->regsR[j] = lookupHRegRemap(map, details->regsR[j]);
   for (j = 0; j < tmpl->nscr; j++)
      details->regsS[j] = lookupHRegRemap(map, details->regsS[j]);
   for (j = 0; j < tmpl->narg; j++)
      details->regsA[j] = lookupHRegRemap(map, details->regsA[j]);
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
      RRegSet__pp(set_1, ppHRegGENERIC); vex_printf("\n");
      vex_printf("              # set2: ");
      RRegSet__pp(&set_2, ppHRegGENERIC); vex_printf("\n");
      vex_printf("              # set3: ");
      RRegSet__pp(set_3, ppHRegGENERIC); vex_printf("\n");
      vex_printf("              # set4: ");
      RRegSet__pp(&set_4, ppHRegGENERIC); vex_printf("\n");
      vex_printf("              # pres: ");
      RRegSet__pp(result, ppHRegGENERIC); vex_printf("\n");
   }

   /* Remove any non allocatable registers (see big comment above) */
   RRegSet__deleteNonAllocatable(result);
}


/* Emits host code for the complete NCode block |details| into
   |ab_hot| and |ab_cold|, possibly adding relocation information to
   |rb| too.  The caller must supply a host-dependent function
   |emit_OneNInstr| which generates host code for a single NInstr.
   This function is required to generate <= 1024 bytes of code.
   Returns True if OK, False if not enough buffer space.
*/
Bool HInstrNCode__emit ( /*MOD*/AssemblyBuffer*   ab_hot,
                         /*MOD*/AssemblyBuffer*   ab_cold,
                         /*MOD*/RelocationBuffer* rb,
                         const HInstrNCode* details,
                         Bool verbose,
                         void (*emit_OneNInstr) (
                            /*MOD*/AssemblyBuffer* ab,
                            /*MOD*/RelocationBuffer* rb,
                            const NInstr* ni,
                            const NRegMap* nregMap,
                            const RRegSet* hregsLiveAfter,
                            /* the next 2 are for debug printing only */
                            Bool verbose, NLabel niLabel
                         )
                       )
 {
   const NCodeTemplate* tmpl           = details->tmpl;
   const RRegSet*       rregsLiveAfter = details->rrLiveAfter;

   NRegMap nregMap;
   nregMap.regsR  = details->regsR;
   nregMap.regsA  = details->regsA;
   nregMap.regsS  = details->regsS;
   nregMap.nRegsR = tmpl->nres;
   nregMap.nRegsA = tmpl->narg;
   nregMap.nRegsS = tmpl->nscr;

   vassert(hregVecLen(nregMap.regsR) == nregMap.nRegsR);
   vassert(hregVecLen(nregMap.regsA) == nregMap.nRegsA);
   vassert(hregVecLen(nregMap.regsS) == nregMap.nRegsS);

   if (AssemblyBuffer__getRemainingSize(ab_hot) < 1024)
      return False;
   if (AssemblyBuffer__getRemainingSize(ab_cold) < 1024)
      return False;
   if (RelocationBuffer__getRemainingSize(rb) < 128)
      return False;

   /* Count how many hot and cold instructions (NInstrs) the template
      has, since we'll need to allocate temporary arrays to keep track
      of the label offsets. */
   UInt nHot  = ninstrVecLen(tmpl->hot);
   UInt nCold = ninstrVecLen(tmpl->cold);

   /* Here are our two arrays for tracking the AssemblyBuffer offsets
      of the NCode instructions. */
   UInt i;
   UInt offsetsHot[nHot];
   UInt offsetsCold[nCold];
   for (i = 0; i < nHot;  i++) offsetsHot[i]  = 0;
   for (i = 0; i < nCold; i++) offsetsCold[i] = 0;

   /* We'll be adding entries to the relocation buffer, |rb|, and will
      need to adjust their |dst| fields after generation of the hot
      and cold code.  Record therefore where we are in the buffer now,
      so that we can iterate over the new entries later. */
   UInt rb_first = RelocationBuffer__getNext(rb);

   /* Generate the hot code */
   for (i = 0; i < nHot; i++) {
      offsetsHot[i] = AssemblyBuffer__getNext(ab_hot);
      NLabel lbl = mkNLabel(Nlz_Hot, i);
      emit_OneNInstr(ab_hot, rb, tmpl->hot[i], &nregMap,
                     rregsLiveAfter, verbose, lbl);
   }   

   /* And the cold code */
   for (i = 0; i < nCold; i++) {
      offsetsCold[i] = AssemblyBuffer__getNext(ab_cold);
      NLabel lbl = mkNLabel(Nlz_Cold, i);
      emit_OneNInstr(ab_cold, rb, tmpl->cold[i], &nregMap,
                     rregsLiveAfter, verbose, lbl);
   }

   /* Now visit the new relocation entries. */
   UInt rb_last1 = RelocationBuffer__getNext(rb);

   for (i = rb_first; i < rb_last1; i++) {
      Relocation* reloc = &rb->buf[i];

      /* Show the reloc before the label-to-offset transformation. */
      if (verbose) {
         vex_printf("   reloc:  ");
         ppRelocation(reloc);
         vex_printf("\n");
      }

      /* Transform the destination component of |reloc| so that it no
         longer refers to a label but rather to an offset in the hot
         or cold assembly buffer. */
      vassert(!reloc->dst.isOffset);
      reloc->dst.isOffset = True;

      if (reloc->dst.zone == Nlz_Hot) {
         vassert(reloc->dst.num < nHot);
         reloc->dst.num = offsetsHot[reloc->dst.num];
      } else {
         vassert(reloc->dst.zone == Nlz_Cold);
         vassert(reloc->dst.num < nCold);
         reloc->dst.num = offsetsCold[reloc->dst.num];
      }

      /* Show the reloc after the label-to-offset transformation. */
      if (verbose) {
         vex_printf("   reloc:  ");
         ppRelocation(reloc);
         vex_printf("\n");
      }
   }

   return True;
}

/*---------------------------------------------------------------*/
/*--- end                                 host_generic_regs.c ---*/
/*---------------------------------------------------------------*/
