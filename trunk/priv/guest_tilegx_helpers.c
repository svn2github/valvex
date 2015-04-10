/*---------------------------------------------------------------*/
/*--- begin                            guest_tilegx_helpers.c ---*/
/*---------------------------------------------------------------*/

/*
  This file is part of Valgrind, a dynamic binary instrumentation
  framework.

  Copyright (C) 2010-2013 Tilera Corp.

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
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
  02111-1307, USA.

  The GNU General Public License is contained in the file COPYING.
*/

/* Contributed by Zhi-Gang Liu <zliu at tilera dot com> */

#include "libvex_basictypes.h"
#include "libvex_emnote.h"
#include "libvex_guest_tilegx.h"
#include "libvex_ir.h"
#include "libvex.h"

#include "main_util.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_tilegx_defs.h"

/* This file contains helper functions for tilegx guest code.  Calls to
   these functions are generated by the back end.
*/

#define ALWAYSDEFD(field)                               \
  { offsetof(VexGuestTILEGXState, field),               \
      (sizeof ((VexGuestTILEGXState*)0)->field) }

/* generalised left-shifter */
static inline UInt lshift ( UInt x, Int n )
{
  if (n >= 0)
    return x << n;
  else
    return x >> (-n);
}

IRExpr *guest_tilegx_spechelper ( const HChar * function_name, IRExpr ** args,
                                  IRStmt ** precedingStmts, Int n_precedingStmts)
{
  return NULL;
}

/* VISIBLE TO LIBVEX CLIENT */
void LibVEX_GuestTILEGX_initialise ( VexGuestTILEGXState * vex_state )
{
  vex_state->guest_r0 = 0;
  vex_state->guest_r1 = 0;
  vex_state->guest_r2 = 0;
  vex_state->guest_r3 = 0;
  vex_state->guest_r4 = 0;
  vex_state->guest_r5 = 0;
  vex_state->guest_r6 = 0;
  vex_state->guest_r7 = 0;
  vex_state->guest_r8 = 0;
  vex_state->guest_r9 = 0;
  vex_state->guest_r10 = 0;
  vex_state->guest_r11 = 0;
  vex_state->guest_r12 = 0;
  vex_state->guest_r13 = 0;
  vex_state->guest_r14 = 0;
  vex_state->guest_r15 = 0;
  vex_state->guest_r16 = 0;
  vex_state->guest_r17 = 0;
  vex_state->guest_r18 = 0;
  vex_state->guest_r19 = 0;
  vex_state->guest_r20 = 0;
  vex_state->guest_r21 = 0;
  vex_state->guest_r22 = 0;
  vex_state->guest_r23 = 0;
  vex_state->guest_r24 = 0;
  vex_state->guest_r25 = 0;
  vex_state->guest_r26 = 0;
  vex_state->guest_r27 = 0;
  vex_state->guest_r28 = 0;
  vex_state->guest_r29 = 0;
  vex_state->guest_r30 = 0;
  vex_state->guest_r31 = 0;
  vex_state->guest_r32 = 0;
  vex_state->guest_r33 = 0;
  vex_state->guest_r34 = 0;
  vex_state->guest_r35 = 0;
  vex_state->guest_r36 = 0;
  vex_state->guest_r37 = 0;
  vex_state->guest_r38 = 0;
  vex_state->guest_r39 = 0;
  vex_state->guest_r40 = 0;
  vex_state->guest_r41 = 0;
  vex_state->guest_r42 = 0;
  vex_state->guest_r43 = 0;
  vex_state->guest_r44 = 0;
  vex_state->guest_r45 = 0;
  vex_state->guest_r46 = 0;
  vex_state->guest_r47 = 0;
  vex_state->guest_r48 = 0;
  vex_state->guest_r49 = 0;
  vex_state->guest_r50 = 0;
  vex_state->guest_r51 = 0;
  vex_state->guest_r52 = 0;
  vex_state->guest_r53 = 0;
  vex_state->guest_r54 = 0;
  vex_state->guest_r55 = 0;

  vex_state->guest_pc = 0;   /* Program counter */

  vex_state->guest_EMNOTE = 0;
  vex_state->guest_CMSTART = 0;

  /* For clflush: record start and length of area to invalidate */
  vex_state->guest_CMSTART = 0;
  vex_state->guest_CMLEN = 0;

  /* Used to record the unredirected guest address at the start of
     a translation whose start has been redirected.  By reading
     this pseudo-register shortly afterwards, the translation can
     find out what the corresponding no-redirection address was.
     Note, this is only set for wrap-style redirects, not for
     replace-style ones. */
  vex_state->guest_NRADDR = 0;
}

/*-----------------------------------------------------------*/
/*--- Describing the tilegx guest state, for the benefit    ---*/
/*--- of iropt and instrumenters.                         ---*/
/*-----------------------------------------------------------*/

/* Figure out if any part of the guest state contained in minoff
   .. maxoff requires precise memory exceptions.  If in doubt return
   True (but this is generates significantly slower code).

   We enforce precise exns for guest SP, PC.
*/
Bool guest_tilegx_state_requires_precise_mem_exns (
  Int minoff, Int maxoff,
  VexRegisterUpdates pxControl)
{
  Int sp_min = offsetof(VexGuestTILEGXState, guest_r54);
  Int sp_max = sp_min + 8 - 1;
  Int pc_min = offsetof(VexGuestTILEGXState, guest_pc);
  Int pc_max = pc_min + 8 - 1;

  if (maxoff < sp_min || minoff > sp_max) {
    /* no overlap with sp */
    if (pxControl == VexRegUpdSpAtMemAccess)
      return False;  /* We only need to check stack pointer. */
  } else {
    return True;
  }

  if (maxoff < pc_min || minoff > pc_max) {
    /* no overlap with pc */
  } else {
    return True;
  }

  /* We appear to need precise updates of R52 in order to get proper
     stacktraces from non-optimised code. */
  Int fp_min = offsetof(VexGuestTILEGXState, guest_r52);
  Int fp_max = fp_min + 8 - 1;

  if (maxoff < fp_min || minoff > fp_max) {
    /* no overlap with fp */
  } else {
    return True;
  }

  return False;
}

VexGuestLayout tilegxGuest_layout = {
  /* Total size of the guest state, in bytes. */
  .total_sizeB = sizeof(VexGuestTILEGXState),
  /* Describe the stack pointer. */
  .offset_SP = offsetof(VexGuestTILEGXState, guest_r54),
  .sizeof_SP = 8,
  /* Describe the frame pointer. */
  .offset_FP = offsetof(VexGuestTILEGXState, guest_r52),
  .sizeof_FP = 8,
  /* Describe the instruction pointer. */
  .offset_IP = offsetof(VexGuestTILEGXState, guest_pc),
  .sizeof_IP = 8,
  /* Describe any sections to be regarded by Memcheck as
     'always-defined'. */
  .n_alwaysDefd = 8,
  /* ? :(  */
  .alwaysDefd = {
    /* 0 */ ALWAYSDEFD(guest_r0),
    /* 1 */ ALWAYSDEFD(guest_r1),
    /* 2 */ ALWAYSDEFD(guest_EMNOTE),
    /* 3 */ ALWAYSDEFD(guest_CMSTART),
    /* 4 */ ALWAYSDEFD(guest_CMLEN),
    /* 5 */ ALWAYSDEFD(guest_r52),
    /* 6 */ ALWAYSDEFD(guest_r55),
    /* 7 */ ALWAYSDEFD(guest_pc),
  }
};

#ifdef __tilegx__
ULong tilegx_dirtyhelper_gen ( ULong opc,
                               ULong rd0, ULong rd1,
                               ULong rd2, ULong rd3)
{
  switch (opc)
  {
  case 0:
    {
      /* break point */
      switch (rd0) {
      case 0x286a44ae90048fffULL:
        asm (" bpt ");
        break;
      default:
        vex_printf("unhandled \"bpt\": cins=%016llx\n", rd0);

        vassert(0);
        return 0;
      }
    }
    break;
  case 28:
    {
      return __insn_addxsc(rd1, rd2);
    }
    break;

  case 150:
    {
      __insn_mf();
      return 0;
    }
    break;

  case 152: /* mm rd, ra, imm0, imm1 */
    {
      ULong mask;

      if( rd2 <= rd3)
        mask = (-1ULL << rd2) ^ ((-1ULL << rd3) << 1);
      else
        mask = (-1ULL << rd2) | (-1ULL >> (63 - rd3));

      return (rd0 & mask) | (rd1 & (-1ULL ^ mask));
    }
    break;
  case 154: /* mtspr imm, ra */
    {
      switch(rd0)
      {
      case 0x2785:
        __insn_mtspr(0x2785, rd1);
        break;
      case 0x2780:
        __insn_mtspr(0x2780, rd1);
        break;
      case 0x2708:
        __insn_mtspr(0x2708, rd1);
        break;
      case 0x2580:
        __insn_mtspr(0x2580, rd1);
        break;
      case 0x2581:
        __insn_mtspr(0x2581, rd1);
        break;
      case 0x2709:  // PASS
        __insn_mtspr(0x2709, rd1);
        break;
      case 0x2707:  // FAIL
        __insn_mtspr(0x2707, rd1);
        break;
      case 0x2705:  // DONE
        __insn_mtspr(0x2705, rd1);
        break;

      case 0x2870: //

      default:
        vex_printf("opc=%d rd0=%llx rd1=%llx\n",
                   (int)opc, rd0, rd1);
        vassert(0);
      }
    }
    break;

  case 151: /* mfspr rd, imm */
    {
      switch(rd1)
      {
      case 0x2785:   // SIM_CTRL
        return __insn_mfspr(0x2785);
        break;

      case 0x2708:   // ICS
        return __insn_mfspr(0x2708);
        break;

      case 0x2780:  // CMPEXCH_VALUE
        return __insn_mfspr(0x2780);
        break;

      case 0x2781:  // CYCLE
        return __insn_mfspr(0x2781);
        break;

      case 0x2709:  // PASS
        return __insn_mfspr(0x2709);
        break;

      case 0x2707:  // FAIL
        return __insn_mfspr(0x2707);
        break;

      case 0x2705:  // DONE
        return __insn_mfspr(0x2705);
        break;

      case 0x2580:  // EX_CONTEXT_0
        return __insn_mfspr(0x2580);
        break;

      case 0x2581:  // EX_CONTEXT_1
        return __insn_mfspr(0x2581);
        break;

      default:
        vex_printf("opc=%d rd0=%llx rd1=%llx\n",
                   (int)opc, rd0, rd1);
        vassert(0);
      }
    }
    break;
  case 183:
    {
      return __insn_pcnt(rd1);
    }
    break;
  case 184:
    {
      return __insn_revbits(rd1);
    }
    break;
  case 185: /* revbytes rd, ra */
    {
      return __insn_revbytes(rd1);
    }
    break;

  case 102:
    return __insn_fsingle_add1(rd1, rd2);
    break;

  case 103:
    return __insn_fsingle_addsub2(rd0, rd1, rd2);
    break;

  case 104:
    return __insn_fsingle_mul1(rd1, rd2);
    break;

  case 105:
    return __insn_fsingle_mul2(rd1, rd2);
    break;

  case 106:
    return __insn_fsingle_pack1(rd1);
    break;

  case 107:
    return __insn_fsingle_pack2(rd1, rd2);
    break;

  case 108:
    return __insn_fsingle_sub1(rd1, rd2);
    break;

  case 21:
    switch (rd0) {
    case 0x286a44ae90048fffULL:
      asm ("{ moveli zero, 72 ; raise }");
      break;
    default:
      vex_printf("unhandled \"raise\": cins=%016llx\n", rd0);
      __insn_ill();
      return 0;
    }
    break;

  case 64:
    {
      return __insn_cmul(rd1, rd2);
    }
    break;
  case 65:
    {
      return __insn_cmula(rd0, rd1, rd2);
    }
    break;
  case 66:
    {
      return __insn_cmulaf(rd0, rd1, rd2);
    }
    break;
  case 67:
    {
      return __insn_cmulf(rd1, rd2);
    }
    break;
  case 68:
    {
      return __insn_cmulfr(rd1, rd2);
    }
    break;
  case 69:
    {
      return __insn_cmulh(rd1, rd2);
    }
    break;
  case 70:
    {
      return __insn_cmulhr(rd1, rd2);
    }
    break;
  case 71:
    {
      return __insn_crc32_32(rd1, rd2);
    }
    break;
  case 72:
    {
      return __insn_crc32_8(rd1, rd2);
    }
    break;
  case 75:
    {
      return __insn_dblalign2(rd1, rd2);
    }
    break;
  case 76:
    {
      return __insn_dblalign4(rd1, rd2);
    }
    break;
  case 77:
    {
      return __insn_dblalign6(rd1, rd2);
    }
    break;
  case 78:
    {
      __insn_drain();
      return 0;
    }
    break;
  case 79:
    {
      __insn_dtlbpr(rd0);
      return 0;
    }
    break;
  case 82:
    {
      return __insn_fdouble_add_flags(rd1, rd2);
    }
    break;
  case 83:
    {
      return __insn_fdouble_addsub(rd0, rd1, rd2);
    }
    break;
  case 84:
    {
      return __insn_fdouble_mul_flags(rd1, rd2);
    }
    break;
  case 85:
    {
      return __insn_fdouble_pack1(rd1, rd2);
    }
    break;
  case 86:
    {
      return __insn_fdouble_pack2(rd0, rd1, rd2);
    }
    break;
  case 87:
    {
      return __insn_fdouble_sub_flags(rd1, rd2);
    }
    break;
  case 88:
    {
      return __insn_fdouble_unpack_max(rd1, rd2);
    }
    break;
  case 89:
    {
      return __insn_fdouble_unpack_min(rd1, rd2);
    }
    break;

  case 98:
    {
      __insn_finv(rd0);
      return 0;
    }
    break;
  case 99:
    {
      __insn_flush(rd0);
      return 0;
    }
    break;
  case 100:
    {
      __insn_flushwb();
      return 0;
    }
    break;

  case 109:
    {
      __insn_icoh((ULong *)rd0);
      return 0;
    }
    break;
  case 110:
    {
      __insn_ill();
    }
    break;
  case 111:
    {
      __insn_inv((ULong *)rd0);
      return 0;
    }
    break;

  case 169:
    {
      return __insn_mula_hu_hu(rd0, rd1, rd2);
    }
    break;
  case 170:
    {
      return __insn_mula_hu_ls(rd0, rd1, rd2);
    }
    break;
  case 205:
    {
      return __insn_shufflebytes(rd0, rd1, rd2);
    }
    break;
  case 224:
    {
      return __insn_subxsc(rd1, rd2);
    }
    break;
  case 229:
    {
      return __insn_tblidxb0(rd0, rd1);
    }
    break;
  case 230:
    {
      return __insn_tblidxb1(rd0, rd1);
    }
    break;
  case 231:
    {
      return __insn_tblidxb2(rd0, rd1);
    }
    break;
  case 232:
    {
      return __insn_tblidxb3(rd0, rd1);
    }
    break;
  case 233:
    {
      return __insn_v1add(rd1, rd2);
    }
    break;
  case 234:
    {
      return __insn_v1add(rd1, rd2);
    }
    break;
  case 235:
    {
      return __insn_v1adduc(rd1, rd2);
    }
    break;
  case 236:
    {
      return __insn_v1adiffu(rd1, rd2);
    }
    break;
  case 237:
    {
      return __insn_v1avgu(rd1, rd2);
    }
    break;

  case 238:
    {
      return __insn_v1cmpeq(rd1, rd2);
    }
    break;
  case 239:
    {
      return __insn_v1cmpeq(rd1, rd2);
    }
    break;
  case 240:
    {
      return __insn_v1cmples(rd1, rd2);
    }
    break;
  case 241:
    {
      return __insn_v1cmpleu(rd1, rd2);
    }
    break;
  case 242:
    {
      return __insn_v1cmplts(rd1, rd2);
    }
    break;
  case 243:
    {
      return __insn_v1cmplts(rd1, rd2);
    }
    break;
  case 244:
    {
      return __insn_v1cmpltu(rd1, rd2);
    }
    break;
  case 245:
    {
      return __insn_v1cmpltu(rd1, rd2);
    }
    break;
  case 246:
    {
      return __insn_v1cmpne(rd1, rd2);
    }
    break;
  case 247:
    {
      return __insn_v1ddotpu(rd1, rd2);
    }
    break;
  case 248:
    {
      return __insn_v1ddotpua(rd0, rd1, rd2);
    }
    break;
  case 249:
    {
      return __insn_v1ddotpus(rd1, rd2);
    }
    break;
  case 250:
    {
      return __insn_v1ddotpusa(rd0, rd1, rd2);
    }
    break;
  case 251:
    {
      return __insn_v1dotp(rd1, rd2);
    }
    break;
  case 252:
    {
      return __insn_v1dotpa(rd0, rd1, rd2);
    }
    break;
  case 253:
    {
      return __insn_v1dotpu(rd1, rd2);
    }
    break;
  case 254:
    {
      return __insn_v1dotpua(rd0, rd1, rd2);
    }
    break;
  case 255:
    {
      return __insn_v1dotpus(rd1, rd2);
    }
    break;
  case 256:
    {
      return __insn_v1dotpusa(rd0, rd1, rd2);
    }
    break;
  case 257:
    {
      return __insn_v1int_h(rd1, rd2);
    }
    break;
  case 258:
    {
      return __insn_v1int_l(rd1, rd2);
    }
    break;
  case 259:
    {
      return __insn_v1maxu(rd1, rd2);
    }
    break;
  case 260:
    {
      return __insn_v1maxu(rd1, rd2);
    }
    break;
  case 261:
    {
      return __insn_v1minu(rd1, rd2);
    }
    break;
  case 262:
    {
      return __insn_v1minu(rd1, rd2);
    }
    break;
  case 263:
    {
      return __insn_v1mnz(rd1, rd2);
    }
    break;
  case 264:
    {
      return __insn_v1multu(rd1, rd2);
    }
    break;
  case 265:
    {
      return __insn_v1mulu(rd1, rd2);
    }
    break;
  case 266:
    {
      return __insn_v1mulus(rd1, rd2);
    }
    break;
  case 267:
    {
      return __insn_v1mz(rd1, rd2);
    }
    break;
  case 268:
    {
      return __insn_v1sadau(rd0, rd1, rd2);
    }
    break;
  case 269:
    {
      return __insn_v1sadu(rd1, rd2);
    }
    break;
  case 270:
    {
      return __insn_v1shl(rd1, rd2);
    }
    break;
  case 271:
    {
      return __insn_v1shli(rd1, rd2);
    }
    break;
  case 272:
    {
      return __insn_v1shrs(rd1, rd2);
    }
    break;
  case 273:
    {
      return __insn_v1shrsi(rd1, rd2);
    }
    break;
  case 274:
    {
      return __insn_v1shru(rd1, rd2);
    }
    break;
  case 275:
    {
      return __insn_v1shrui(rd1, rd2);
    }
    break;
  case 276:
    {
      return __insn_v1sub(rd1, rd2);
    }
    break;
  case 277:
    {
      return __insn_v1subuc(rd1, rd2);
    }
    break;
  case 278:
    {
      return __insn_v2add(rd1, rd2);
    }
    break;
  case 279:
    {
      return __insn_v2add(rd1, rd2);
    }
    break;
  case 280:
    {
      return __insn_v2addsc(rd1, rd2);
    }
    break;
  case 281:
    {
      return __insn_v2adiffs(rd1, rd2);
    }
    break;
  case 282:
    {
      return __insn_v2avgs(rd1, rd2);
    }
    break;
  case 283:
    {
      return __insn_v2cmpeq(rd1, rd2);
    }
    break;
  case 284:
    {
      return __insn_v2cmpeq(rd1, rd2);
    }
    break;
  case 285:
    {
      return __insn_v2cmples(rd1, rd2);
    }
    break;
  case 286:
    {
      return __insn_v2cmpleu(rd1, rd2);
    }
    break;
  case 287:
    {
      return __insn_v2cmplts(rd1, rd2);
    }
    break;
  case 288:
    {
      return __insn_v2cmplts(rd1, rd2);
    }
    break;
  case 289:
    {
      return __insn_v2cmpltu(rd1, rd2);
    }
    break;
  case 290:
    {
      return __insn_v2cmpltu(rd1, rd2);
    }
    break;
  case 291:
    {
      return __insn_v2cmpne(rd1, rd2);
    }
    break;
  case 292:
    {
      return __insn_v2dotp(rd1, rd2);
    }
    break;
  case 293:
    {
      return __insn_v2dotpa(rd0, rd1, rd2);
    }
    break;
  case 294:
    {
      return __insn_v2int_h(rd1, rd2);
    }
    break;
  case 295:
    {
      return __insn_v2int_l(rd1, rd2);
    }
    break;
  case 296:
    {
      return __insn_v2maxs(rd1, rd2);
    }
    break;
  case 297:
    {
      return __insn_v2maxs(rd1, rd2);
    }
    break;
  case 298:
    {
      return __insn_v2mins(rd1, rd2);
    }
    break;
  case 299:
    {
      return __insn_v2mins(rd1, rd2);
    }
    break;
  case 300:
    {
      return __insn_v2mnz(rd1, rd2);
    }
    break;
  case 301:
    {
      return __insn_v2mulfsc(rd1, rd2);
    }
    break;
  case 302:
    {
      return __insn_v2muls(rd1, rd2);
    }
    break;
  case 303:
    {
      return __insn_v2mults(rd1, rd2);
    }
    break;
  case 304:
    {
      return __insn_v2mz(rd1, rd2);
    }
    break;
  case 305:
    {
      return __insn_v2packh(rd1, rd2);
    }
    break;
  case 306:
    {
      return __insn_v2packl(rd1, rd2);
    }
    break;
  case 307:
    {
      return __insn_v2packuc(rd1, rd2);
    }
    break;
  case 308:
    {
      return __insn_v2sadas(rd0, rd1, rd2);
    }
    break;
  case 309:
    {
      return __insn_v2sadau(rd0, rd1, rd2);
    }
    break;
  case 310:
    {
      return __insn_v2sads(rd1, rd2);
    }
    break;
  case 311:
    {
      return __insn_v2sadu(rd1, rd2);
    }
    break;
  case 312:
    {
      return __insn_v2shl(rd1, rd2);
    }
    break;
  case 313:
    {
      return __insn_v2shli(rd1, rd2);
    }
    break;
  case 314:
    {
      return __insn_v2shlsc(rd1, rd2);
    }
    break;
  case 315:
    {
      return __insn_v2shrs(rd1, rd2);
    }
    break;
  case 316:
    {
      return __insn_v2shrsi(rd1, rd2);
    }
    break;
  case 317:
    {
      return __insn_v2shru(rd1, rd2);
    }
    break;
  case 318:
    {
      return __insn_v2shrui(rd1, rd2);
    }
    break;
  case 319:
    {
      return __insn_v2sub(rd1, rd2);
    }
    break;
  case 320:
    {
      return __insn_v2subsc(rd1, rd2);
    }
    break;
  case 321:
    {
      return __insn_v4add(rd1, rd2);
    }
    break;
  case 322:
    {
      return __insn_v4addsc(rd1, rd2);
    }
    break;
  case 323:
    {
      return __insn_v4int_h(rd1, rd2);
    }
    break;
  case 324:
    {
      return __insn_v4int_l(rd1, rd2);
    }
    break;
  case 325:
    {
      return __insn_v4packsc(rd1, rd2);
    }
    break;
  case 326:
    {
      return __insn_v4shl(rd1, rd2);
    }
    break;
  case 327:
    {
      return __insn_v4shlsc(rd1, rd2);
    }
    break;
  case 328:
    {
      return __insn_v4shrs(rd1, rd2);
    }
    break;
  case 329:
    {
      return __insn_v4shru(rd1, rd2);
    }
    break;
  case 330:
    {
      return __insn_v4sub(rd1, rd2);
    }
    break;
  case 331:
    {
      return __insn_v4subsc(rd1, rd2);
    }
    break;

  default:
    vex_printf("opc=%d rd0=%llx rd1=%llx\n",
               (int)opc, rd0, rd1);
    vassert(0);
  }
}
#else
ULong tilegx_dirtyhelper_gen ( ULong opc,
                               ULong rd0, ULong rd1,
                               ULong rd2, ULong rd3 )
{
  vex_printf("NOT a TILEGX platform");
  return 0;
}
#endif /* __tilegx__ */

/*---------------------------------------------------------------*/
/*--- end                              guest_tilegx_helpers.c ---*/
/*---------------------------------------------------------------*/
