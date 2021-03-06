// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, INRIA Paris-Rocquencourt
//
// Copyright (c) 2013 Institut National de Recherche en Informatique et
//  en Automatique.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the <organization> nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
// HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// *********************************************************************

// Helper functions for 64-bit integer arithmetic.  IA32 version.

#include "sysdeps.h"

// Signed division

FUNCTION(__i64_sdiv)
        pushl %ebp
        pushl %esi
        pushl %edi
        movl 20(%esp), %esi          // esi = NH
        movl %esi, %ebp              // save sign of N in ebp
        testl %esi, %esi
        jge 1f                       // if N < 0,
        negl 16(%esp)                // N = -N
        adcl $0, %esi
        negl %esi
        movl %esi, 20(%esp)
1:      movl 28(%esp), %esi          // esi = DH
        xorl %esi, %ebp              // sign of result in ebp
        testl %esi, %esi
        jge 2f                       // if D < 0,
        negl 24(%esp)                // D = -D
        adcl $0, %esi
        negl %esi
        movl %esi, 28(%esp)
2:      call GLOB(__i64_udivmod)
        testl %ebp, %ebp             // apply sign to result
        jge 3f
        negl %esi
        adcl $0, %edi
        negl %edi
3:      movl %esi, %eax
        movl %edi, %edx
        popl %edi
        popl %esi
        popl %ebp
        ret
ENDFUNCTION(__i64_sdiv)
