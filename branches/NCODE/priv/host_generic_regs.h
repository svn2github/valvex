
/*---------------------------------------------------------------*/
/*--- begin                               host_generic_regs.h ---*/
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

#ifndef __VEX_HOST_GENERIC_REGS_H
#define __VEX_HOST_GENERIC_REGS_H

#include "libvex_basictypes.h"


/*---------------------------------------------------------*/
/*--- Representing HOST REGISTERS                       ---*/
/*---------------------------------------------------------*/

/* Host registers.  Stuff to represent:

   - The register index.  This is a zero-based, sequential index that
     facilitates indexing into arrays or virtual or real registers.
     Virtual and real registers both have indices starting at zero.
     Interpreting a real register index requires having the host's
     RRegUniverse to hand.

   - The register's hardware encoding.  This applies only for real
     registers and should be zero for virtual registers.  This is the
     number as used in a target architecture encoding.

   - The register class

   - Whether or not the register is a virtual reg.

   Registers are sized so as to fit into 32 bits.

   Note that since the class field is never 1111b, no valid register
   can have the value INVALID_HREG.

   There are currently 6 register classes:

     int32 int64 float32 float64 simd64 simd128
*/

/* Registers are represented as 32 bit integers, with the following layout:

   31     30..27  26..20  19..0
   isV:1  rc:4    enc:7   ix:20

   where
      UInt      ix:20;   // Zero based index
      UInt      enc:7;   // Hardware encoding number
      HRegClass rc:4;    // the register's HRegClass
      Bool      isV:1;   // is it a virtual register?

   The obvious thing to do here would be to use bitfields.  But gcc
   seems to have problems constant folding calls to mkHReg() with all
   4 parameters constant to a 32 bit number, when using bitfields.
   Hence the use of the traditional shift-and-mask by-hand bitfields
   instead.
*/
typedef  struct { UInt u32; }  HReg;

/* HRegClass describes host register classes which the instruction
   selectors can speak about.  We would not expect all of them to be
   available on any specific host.  For example on x86, the available
   classes are: Int32, Flt64, Vec128 only.

   IMPORTANT NOTE: host_generic_reg_alloc2.c needs how much space is
   needed to spill each class of register.  It allocates the following
   amount of space:

      HRcInt32     64 bits
      HRcInt64     64 bits
      HRcFlt32     64 bits
      HRcFlt64     128 bits (on x86 these are spilled by fstpt/fldt and
                             so won't fit in a 64-bit slot)
      HRcVec64     64 bits
      HRcVec128    128 bits

   If you add another regclass, you must remember to update
   host_generic_reg_alloc2.c accordingly.  

   When adding entries to enum HRegClass, do not use any value > 14 or < 1.
*/
typedef
   enum { 
      HRcINVALID=1,   /* NOT A VALID REGISTER CLASS */
      HRcInt32=3,     /* 32-bit int */
      HRcInt64=4,     /* 64-bit int */
      HRcFlt32=5,     /* 32-bit float */
      HRcFlt64=6,     /* 64-bit float */
      HRcVec64=7,     /* 64-bit SIMD */
      HRcVec128=8     /* 128-bit SIMD */
   }
   HRegClass;

extern void ppHRegClass ( HRegClass );


/* Print an HReg in a generic (non-target-specific) way. */
extern void ppHReg ( HReg );

/* Construct.  The goal here is that compiler can fold this down to a
   constant in the case where the four arguments are constants, which
   is often the case. */
static inline HReg mkHReg ( Bool virtual, HRegClass rc, UInt enc, UInt ix )
{
   vassert(ix <= 0xFFFFF);
   vassert(enc <= 0x7F);
   vassert(((UInt)rc) <= 0xF);
   vassert(((UInt)virtual) <= 1);
   if (virtual) vassert(enc == 0);
   HReg r;
   r.u32 = ((((UInt)virtual) & 1)       << 31)  |
           ((((UInt)rc)      & 0xF)     << 27)  |
           ((((UInt)enc)     & 0x7F)    << 20)  |
           ((((UInt)ix)      & 0xFFFFF) << 0);
   return r;
}

static inline HRegClass hregClass ( HReg r )
{
   HRegClass rc = (HRegClass)((r.u32 >> 27) & 0xF);
   vassert(rc >= HRcInt32 && rc <= HRcVec128);
   return rc;
}

static inline UInt hregIndex ( HReg r )
{
   return r.u32 & 0xFFFFF;
}

static inline UInt hregEncoding ( HReg r )
{
   return (r.u32 >> 20) & 0x7F;
}

static inline Bool hregIsVirtual ( HReg r )
{
   return toBool((r.u32 >> 31) & 1);
}

static inline Bool sameHReg ( HReg r1, HReg r2 )
{
   return toBool(r1.u32 == r2.u32);
}

static const HReg HReg_INVALID = { .u32 = 0xFFFFFFFF };

static inline Bool hregIsInvalid ( HReg r )
{
   return sameHReg(r, HReg_INVALID);
}


/*---------------------------------------------------------*/
/*--- Real Register Universes                           ---*/
/*---------------------------------------------------------*/

/* A "Real Register Universe" is a read-only structure that contains
   all information about real registers on a given host.  It serves
   several purposes:

   * defines the mapping from real register indices to the registers
     themselves

   * defines the size of the initial section of that mapping that is
     available to the register allocator for use, so that the register
     allocator can treat the registers under its control as a zero
     based, contiguous array.  This is important for its efficiency.

   * gives meaning to RRegSets, which otherwise would merely be a
     bunch of bits.

   This is a big structure, but it's readonly, and we expect to
   allocate only one instance for each run of Valgrind.  It is sized
   so as to be able to deal with up to 64 real registers.  AFAICS none
   of the back ends actually mention more than 64, despite the fact
   that many of the host architectures have more than 64 registers
   when all classes are taken into consideration.
*/

#define N_RREGUNIVERSE_REGS 64

typedef
   struct {
      /* Total number of registers in this universe .. */
      UInt size;
      /* .. of which the first |allocable| are available to regalloc. */
      UInt allocable;
      /* The registers themselves.  All must be real registers, and
         all must have their index number (.s.ix) equal to the array
         index here, since this is the only place where we map index
         numbers to actual registers. */
      HReg regs[N_RREGUNIVERSE_REGS];
   }
   RRegUniverse;

/* Nominally initialise (zero out) an RRegUniverse. */
void RRegUniverse__init ( /*OUT*/RRegUniverse* );

/* Check an RRegUniverse is valid, and assert if not.*/
void RRegUniverse__check_is_sane ( const RRegUniverse* );

/* Print an RRegUniverse, for debugging. */
void RRegUniverse__pp ( const RRegUniverse* );


/*---------------------------------------------------------*/
/*--- Real Register Sets                                ---*/
/*---------------------------------------------------------*/

/* Represents sets of real registers.  |bits| is interpreted in the
   context of |univ|.  That is, each bit index |i| in |bits|
   corresponds to the register |univ->regs[i]|.  This relies
   entirely on the fact that N_RREGUNIVERSE_REGS <= 64.

   It would have been nice to have been able to make this abstract,
   but it is necessary to declare globals of this type.  Hence the
   size has to be known to the users of the type and so it can't be
   abstract.
*/
typedef
   struct {
      ULong               bits;
      const RRegUniverse* univ;
   }
   RRegSet;

STATIC_ASSERT(N_RREGUNIVERSE_REGS <= 8 * sizeof(ULong));


/* Print a register set, using the arch-specific register printing
   function |regPrinter| supplied. */
extern void RRegSet__pp ( const RRegSet* set, void (*regPrinter)(HReg) );

/* Initialise an RRegSet, making it empty. */
extern void RRegSet__init ( /*OUT*/RRegSet* set, const RRegUniverse* univ );

/* Create a new, empty, set, in the normal (transient) heap. */
extern RRegSet* RRegSet__new ( const RRegUniverse* univ );

/* Return the RRegUniverse for a given RRegSet. */
extern const RRegUniverse* RRegSet__getUniverse ( const RRegSet* );

/* Install elements from vec[0 .. nVec-1].  The previous contents of
   |dst| are lost. */
extern void RRegSet__fromVec ( /*MOD*/RRegSet* dst,
                               const HReg* vec, UInt nVec );

/* Copy the contents of |regs| into |dst|.  The previous contents of
   |dst| are lost. */
extern void RRegSet__copy ( /*MOD*/RRegSet* dst, const RRegSet* regs );

/* Add |reg| to |dst|. */
extern void RRegSet__add ( /*MOD*/RRegSet* dst, HReg reg );

/* Remove |reg| from |dst|. */
extern void RRegSet__del ( /*MOD*/RRegSet* dst, HReg reg );

/* Add |regs| to |dst|. */
extern void RRegSet__plus ( /*MOD*/RRegSet* dst, const RRegSet* regs );

/* Remove |regs| from |dst|. */
extern void RRegSet__minus ( /*MOD*/RRegSet* dst, const RRegSet* regs );

/* Returns the number of elements in |set|. */
extern UInt RRegSet__card ( const RRegSet* set );

/* Remove non-allocatable registers from this set.  Because the set
   carries its register universe, we can consult that to find the
   non-allocatable registers, so no other parameters are needed. */
extern void RRegSet__deleteNonAllocatable ( /*MOD*/RRegSet* set );


/* Iterating over RRegSets. */
/* ABSTYPE */
typedef  struct _RRegSetIterator  RRegSetIterator;

/* Create a new iterator.  It must be initialised with __init before
   it can be used in __next calls.  This is checked in __next. */
extern RRegSetIterator* RRegSetIterator__new ( void );

/* Initialise an iterator for iterating over the given set. */
extern void RRegSetIterator__init ( /*OUT*/RRegSetIterator* iter,
                                    const RRegSet* set );

/* Get the next element out of an iterator.  If there are no more
   elements, HReg_INVALID is returned.  This pretty much implies (and
   is checked) that the set construction routines above cannot be used
   to insert HReg_INVALID into a set. */
extern HReg RRegSetIterator__next ( /*MOD*/RRegSetIterator* );


/*---------------------------------------------------------*/
/*--- Recording register usage (for reg-alloc)          ---*/
/*---------------------------------------------------------*/

typedef
   enum { HRmRead, HRmWrite, HRmModify }
   HRegMode;


/* This isn't entirely general, and is specialised towards being fast,
   for the reg-alloc.  It represents real registers using a bitmask
   and can also represent up to four virtual registers, in an
   unordered array.  This is based on the observation that no
   instruction that we generate can mention more than four registers
   at once. 
*/
#define N_HREGUSAGE_VREGS 5

typedef
   struct {
      /* The real registers.  The associated universe is not stored
         here -- callers will have to pass it around separately, as
         needed. */
      ULong    rRead;     /* real regs that are read */
      ULong    rWritten;  /* real regs that are written */
      /* The virtual registers. */
      HReg     vRegs[N_HREGUSAGE_VREGS];
      HRegMode vMode[N_HREGUSAGE_VREGS];
      UInt     n_vRegs;
   }
   HRegUsage;

extern void ppHRegUsage ( const RRegUniverse*, HRegUsage* );

static inline void initHRegUsage ( HRegUsage* tab )
{
   tab->rRead    = 0;
   tab->rWritten = 0;
   tab->n_vRegs  = 0;
}

/* Add a register to a usage table.  Combine incoming read uses with
   existing write uses into a modify use, and vice versa.  Do not
   create duplicate entries -- each reg should only be mentioned once.  
*/
extern void addHRegUse ( HRegUsage*, HRegMode, HReg );

extern Bool HRegUsage__contains ( const HRegUsage*, HReg );

extern void addHRegUse_from_RRegSet ( HRegUsage*, HRegMode, const RRegSet* );


/*---------------------------------------------------------*/
/*--- Indicating register remappings (for reg-alloc)    ---*/
/*---------------------------------------------------------*/

/* Note that such maps can only map virtual regs to real regs.
   addToHRegRenap will barf if given a pair not of that form.  As a
   result, no valid HRegRemap will bind a real reg to anything, and so
   if lookupHRegMap is given a real reg, it returns it unchanged.
   This is precisely the behaviour that the register allocator needs
   to impose its decisions on the instructions it processes.  */

#define N_HREG_REMAP 6

typedef
   struct {
      HReg orig       [N_HREG_REMAP];
      HReg replacement[N_HREG_REMAP];
      Int  n_used;
   }
   HRegRemap;

extern void ppHRegRemap     ( HRegRemap* );
extern void addToHRegRemap  ( HRegRemap*, HReg, HReg );
extern HReg lookupHRegRemap ( HRegRemap*, HReg );

static inline void initHRegRemap ( HRegRemap* map )
{
   map->n_used = 0;
}


/*---------------------------------------------------------*/
/*--- Abstract instructions                             ---*/
/*---------------------------------------------------------*/

/* A type is needed to refer to pointers to instructions of any
   target.  Defining it like this means that HInstr* can stand in for
   X86Instr*, ArmInstr*, etc. */

typedef  void  HInstr;


/* An expandable array of HInstr*'s.  Handy for insn selection and
   register allocation.  n_vregs indicates the number of virtual
   registers mentioned in the code, something that reg-alloc needs to
   know.  These are required to be numbered 0 .. n_vregs-1. 
*/
typedef
   struct {
      HInstr** arr;
      Int      arr_size;
      Int      arr_used;
      Int      n_vregs;
   }
   HInstrArray;

extern HInstrArray* newHInstrArray ( void );

/* Never call this directly.  It's the slow and incomplete path for
   addHInstr. */
__attribute__((noinline))
extern void addHInstr_SLOW ( HInstrArray*, HInstr* );

static inline void addHInstr ( HInstrArray* ha, HInstr* instr )
{
   if (LIKELY(ha->arr_used < ha->arr_size)) {
      ha->arr[ha->arr_used] = instr;
      ha->arr_used++;
   } else {
      addHInstr_SLOW(ha, instr);
   }
}


/*---------------------------------------------------------*/
/*--- C-Call return-location descriptions               ---*/
/*---------------------------------------------------------*/

/* This is common to all back ends.  It describes where the return
   value from a C call is located.  This is important in the case that
   the call is conditional, since the return locations will need to be
   set to 0x555..555 in the case that the call does not happen. */

typedef
   enum {
      RLPri_INVALID,   /* INVALID */
      RLPri_None,      /* no return value (a.k.a C "void") */
      RLPri_Int,       /* in the primary int return reg */
      RLPri_2Int,      /* in both primary and secondary int ret regs */
      RLPri_V128SpRel, /* 128-bit value, on the stack */
      RLPri_V256SpRel  /* 256-bit value, on the stack */
   }
   RetLocPrimary;

typedef
   struct {
      /* Primary description */
      RetLocPrimary pri;
      /* For .pri == RLPri_V128SpRel or RLPri_V256SpRel only, gives
         the offset of the lowest addressed byte of the value,
         relative to the stack pointer.  For all other .how values,
         has no meaning and should be zero. */
      Int spOff;
   }
   RetLoc;

extern void ppRetLoc ( RetLoc rloc );

static inline RetLoc mk_RetLoc_simple ( RetLocPrimary pri ) {
   vassert(pri >= RLPri_INVALID && pri <= RLPri_2Int);
   return (RetLoc){pri, 0};
}

static inline RetLoc mk_RetLoc_spRel ( RetLocPrimary pri, Int off ) {
   vassert(pri >= RLPri_V128SpRel && pri <= RLPri_V256SpRel);
   return (RetLoc){pri, off};
}

static inline Bool is_sane_RetLoc ( RetLoc rloc ) {
   switch (rloc.pri) {
      case RLPri_None: case RLPri_Int: case RLPri_2Int:
         return rloc.spOff == 0;
      case RLPri_V128SpRel: case RLPri_V256SpRel:
         return True;
      default:
         return False;
   }
}

static inline RetLoc mk_RetLoc_INVALID ( void ) {
   return (RetLoc){RLPri_INVALID, 0};
}

static inline Bool is_RetLoc_INVALID ( RetLoc rl ) {
   return rl.pri == RLPri_INVALID && rl.spOff == 0;
}


/*---------------------------------------------------------*/
/*--- Assembly buffers                                  ---*/
/*---------------------------------------------------------*/

/* This describes a buffer into which instructions are assembled. */

typedef
   struct {
      UChar* buf;     /* buffer */
      UInt   bufSize; /* max allowable size */
      UInt   bufUsed; /* next free location */
   }
   AssemblyBuffer;

static inline void AssemblyBuffer__init ( /*OUT*/AssemblyBuffer* abuf,
                                          UChar* buf, UInt bufSize )
{
   abuf->buf     = buf;
   abuf->bufSize = bufSize;
   abuf->bufUsed = 0;
}

static inline UChar* AssemblyBuffer__getCursor ( const AssemblyBuffer* abuf )
{
   return &abuf->buf[abuf->bufUsed];
}

static inline UInt* AssemblyBuffer__getCursor_4aligned ( const
                                                         AssemblyBuffer* abuf )
{
   UChar* addr = &abuf->buf[abuf->bufUsed];
   vassert(IS_4_ALIGNED(addr));
   /* Cast via HWord so that gcc on arm32 doesn't complain about the
      increase of alignment requirements. */
   return (UInt*)(HWord)addr;
}

static inline UInt AssemblyBuffer__getNext ( const AssemblyBuffer* abuf )
{
   return abuf->bufUsed;
}

static 
inline Int AssemblyBuffer__getRemainingSize ( const AssemblyBuffer* abuf )
{
   return (Int)abuf->bufSize - (Int)abuf->bufUsed;
}


/*---------------------------------------------------------*/
/*--- Relocations.  Move somewhere else?                ---*/
/*---------------------------------------------------------*/

/* This describes a place at which a relocation is to be performed, by
   pairing a hot/cold zone descriptor and an offset in an assembly
   buffer.
*/
typedef
   struct {
      NLabelZone zone;
      UInt       offset; // in the AssemblyBuffer associated with |zone|
   }
   RelocWhere;

static inline RelocWhere mkRelocWhere ( NLabelZone zone, UInt offset ) {
   RelocWhere rw = { zone, offset };
   return rw;
}


/* This describes a place which is the target of a relocation, that
   is, a jump target.  The target is in the hot or cold code buffer,
   hence |zone|, and is further characterised by |num| either as an
   instruction number (that is, an NLabel) when |isOffset| == False,
   or as an offset in the assembly buffer when |isOffset| == True.

   RelocDsts are initially created with |isOffset| == False, that is,
   as an NLabel.  Once we know the know the AssemblyBuffer offsets for
   each NLabel, |isOffset| is set to True and |num| becomes the
   offset.  Once it is in that form, it is possible to compute the
   distance in bytes between it and a RelocWhere, and hence perform
   the relocation.
*/
typedef
   struct {
      NLabelZone zone;
      UInt       num;
      Bool       isOffset;
   }
   RelocDst;

static inline RelocDst mkRelocDst_from_NLabel ( NLabel nl ) {
   RelocDst rd = { nl.zone, nl.ino, False/*!isOffset*/ };
   return rd;
}


/* What this describes is as follows.  Let |whereA| be an host address
   that |where| evaluates to, by whatever means, and let |dstA|
   likewise be a host address that |dst| evaluates to.

   What this then describes is a modification of a 32 bit integer
   located at whereA[0..3], interpreted in the host's endianness.  The
   32 bit value at that location has bits [bitNoMax .. bitNoMin]
   inclusive replaced by the least significant bits of the following
   expression

      E = (dstA - whereA + sign_extend(bias)) >>signed rshift

   and all other bits of that 32 bit value are left unchanged.
   Observe that this description assumes the relocation expression E
   is signed.  If the bits that we copy out of E and into the 32 bit
   word do not sign extend back to E, then the offset is too large to
   be represented and the relocation cannot be performed.

   The use of |bitNo{Max,Min}| facilitates writing an arbitrary bitfield
   in the middle of (eg) an ARM branch instruction.  For amd64-style
   32-bit branch offsets we expect the values to be 0 and 31
   respectively.

   The use of |rshift| facilitates architectures (eg ARM) that use fixed
   length instructions, and hence require the offset to be stated in
   number of instructions instead of (eg on amd64) number of bytes.

   The use of |bias| is necessary because on some targets (eg amd64) the
   processor expects the branch offset to be stated relative to the
   first byte of the instruction, but |where| points somewhere further
   along the instruction.  Hence we have to add a small negative bias
   to "back up" |where| to the start of the instruction.

   So far, so good.  This does assume that the offset bitfield is
   contiguous (not split into pieces) inside the target instruction.
*/
typedef
   struct {
      RelocWhere where;     // where the relocation should be applied
      UChar      bitNoMin;  // 0 .. 31 inclusive
      UChar      bitNoMax;  // bitNoMin .. 31 inclusive
      RelocDst   dst;       // destination of the (presumed) jump
      Int        bias;      // arbitrary, but in practice very small
      UChar      rshift;    // 0, 1 or 2 only
   }
   Relocation;

static
inline Relocation mkRelocation ( RelocWhere where,
                                 UChar bitNoMin, UChar bitNoMax,
                                 RelocDst dst, Int bias, UChar rshift ) {
   Relocation rl = { where, bitNoMin, bitNoMax, dst, bias, rshift };
   return rl;
}

extern void ppRelocation ( Relocation* rl );


/*---------------------------------------------------------*/
/*--- Relocation buffers                                ---*/
/*---------------------------------------------------------*/

/* This describes a buffer in which relocations are stored. */

typedef
   struct {
      Relocation* buf;     /* buffer */
      UInt        bufSize; /* max allowable size */
      UInt        bufUsed; /* next free location */
   }
   RelocationBuffer;

static inline void RelocationBuffer__init ( /*OUT*/RelocationBuffer* rbuf,
                                            Relocation* buf, UInt bufSize )
{
   rbuf->buf     = buf;
   rbuf->bufSize = bufSize;
   rbuf->bufUsed = 0;
}

static inline UInt RelocationBuffer__getNext ( const RelocationBuffer* rbuf )
{
   return rbuf->bufUsed;
}

static 
inline Int RelocationBuffer__getRemainingSize ( const RelocationBuffer* rbuf )
{
   return (Int)rbuf->bufSize - (Int)rbuf->bufUsed;
}


/*---------------------------------------------------------*/
/*--- Reg alloc: TODO: move somewhere else              ---*/
/*---------------------------------------------------------*/

extern
HInstrArray* doRegisterAllocation (

   /* Incoming virtual-registerised code. */ 
   HInstrArray* instrs_in,

   /* The real-register universe to use.  This contains facts about
      real registers, one of which is the set of registers available
      for allocation. */
   const RRegUniverse* univ,

   /* Return True iff the given insn is a reg-reg move, in which
      case also return the src and dst regs. */
   Bool (*isMove) (const HInstr*, HReg*, HReg*),

   /* Get info about register usage in this insn. */
   void (*getRegUsage) (HRegUsage*, const HInstr*, Bool),

   /* Apply a reg-reg mapping to an insn. */
   void (*mapRegs) (HRegRemap*, HInstr*, Bool),

   /* Return insn(s) to spill/restore a real reg to a spill slot
      offset.  And optionally a function to do direct reloads. */
   void    (*genSpill) (  HInstr**, HInstr**, HReg, Bool, Int, Bool ),
   void    (*genReload) ( HInstr**, HInstr**, HReg, Bool, Int, Bool ),
   HInstr* (*directReload) ( HInstr*, HReg, Short ),
   Int     guest_sizeB,

   /* For debug printing only. */
   void (*ppInstr) ( const HInstr*, Bool ),
   void (*ppReg) ( HReg ),

   /* 32/64bit mode */
   Bool mode64
);


/*---------------------------------------------------------*/
/*--- NCode generation helpers                          ---*/
/*---------------------------------------------------------*/

/* Find the length of a vector of HRegs that is terminated by
   an HReg_INVALID. */
extern UInt hregVecLen ( const HReg* vec );


/* A handy structure to hold the register environment for an NCode
   block -- that is, the NReg to HReg mapping. */
typedef
   struct {
      UInt        nRegsR;
      const HReg* regsR;
      UInt        nRegsA;
      const HReg* regsA;
      UInt        nRegsS;
      const HReg* regsS;
   }
   NRegMap;

/* Find the real (hard) register for |r| by looking up in |map|. */
extern HReg mapNReg ( const NRegMap* map, NReg r );


/* Compute the minimal set of registers to preserve around calls
   embedded within NCode blocks.  See implementation for a detailed
   comment. */
extern
void calcRegistersToPreserveAroundNCodeCall (
        /*OUT*/RRegSet* result,
        const RRegSet*  hregsLiveAfterTheNCodeBlock,
        const RRegSet*  abiCallerSavedRegs,
        const NRegMap*  nregMap,
        NReg nregResHi,
        NReg nregResLo
     );


#endif /* ndef __VEX_HOST_GENERIC_REGS_H */

/*---------------------------------------------------------------*/
/*---                                     host_generic_regs.h ---*/
/*---------------------------------------------------------------*/
