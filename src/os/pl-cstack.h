/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2011, University of Amsterdam
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

#ifndef PL_CSTACK_H_INCLUDED
#define PL_CSTACK_H_INCLUDED

typedef struct c_stack_info
{ int	    initialised;		/* Struct is fully initialized */
  void	   *base;			/* Base of the (C-) stack */
  size_t    size;			/* system (C-) stack */
} c_stack_info;

#if USE_LD_MACROS
#define CStackSize(_)	LDFUNC(CStackSize, _)
#endif /*USE_LD_MACROS*/

COMMON(void)	print_c_backtrace(const char *why);
COMMON(struct btrace *)	save_backtrace(const char *why);
COMMON(void)	btrace_destroy(struct btrace *bt);
COMMON(void)	print_backtrace(int last);		/* 1..SAVE_TRACES */
COMMON(void)	print_backtrace_named(const char *why);
COMMON(void)	initBackTrace(void);
COMMON(void)	sigCrashHandler(int sig);

#define LDFUNC_DECLARATIONS
c_stack_info   *CStackSize(void);
#undef LDFUNC_DECLARATIONS

#endif /*PL_CSTACK_H_INCLUDED*/
