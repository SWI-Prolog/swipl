/*  $Id$

    Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        wielemak@scienc.uva.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 1985-2006, University of Amsterdam

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public
    License as published by the Free Software Foundation; either
    version 2.1 of the License, or (at your option) any later version.

    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

/*#define O_SECURE 1*/
/*#define O_DEBUG 1*/
#include "pl-incl.h"

#undef LD
#define LD LOCAL_LD

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
This module defines support  predicates  for  the  Prolog  all-solutions
predicates findall/3, bagof/3 and setof/3.  These predicates are:

	$record_bag(Key, Value)		Record a value under a key.
    	$collect_bag(Bindings, Values)	Retract all Solutions matching
					Bindings.

The (toplevel) remainder of the all-solutions predicates is  written  in
Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

#define alist LD->bags.bags		/* Each thread has its own */
					/* storage for this */

typedef struct assoc
{ Record record;
  struct assoc *next;
} *Assoc;


static void
freeAssoc(Assoc prev, Assoc a ARG_LD)
{ if ( prev == NULL )
  { alist = a->next;
  } else
    prev->next = a->next;

  if ( a->record )
    freeRecord(a->record);

  freeHeap(a, sizeof(*a));
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
$record_bag(Key-Value)

Record a solution of bagof.  Key is a term  v(V0,  ...Vn),  holding  the
variable binding for solution `Gen'.  Key is ATOM_mark for the mark.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static
PRED_IMPL("$record_bag", 1, record_bag, 0)
{ PRED_LD
  Assoc a = allocHeap(sizeof(*a));

  if ( PL_is_atom(A1) )			/* mark */
  { a->record = 0;
  } else
    a->record = compileTermToHeap(A1, 0);

  DEBUG(1, { Sdprintf("Recorded %p: ", a->record);
	     PL_write_term(Serror, A1, 1200, PL_WRT_ATTVAR_WRITE);
	     Sdprintf("\n");
	   });

  a->next    = alist;
  alist      = a;

  succeed;
}

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
This predicate will fail if no more records are left before the mark.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static
PRED_IMPL("$collect_bag", 2, collect_bag, 0)
{ PRED_LD
  
  term_t bindings = A1;
  term_t bag = A2;

  term_t var_term = PL_new_term_refs(4);	/* v() term on global stack */
  term_t list     = var_term+1;			/* list to construct */
  term_t binding  = var_term+2;			/* binding */
  term_t tmp      = var_term+3;
  Assoc a, next;
  Assoc prev = NULL;
  
  if ( !(a = alist) )
    fail;
  if ( !a->record )
  { freeAssoc(prev, a PASS_LD);
    fail;				/* trapped the mark */
  }

  PL_put_nil(list);
					/* get variable term on global stack */
  copyRecordToGlobal(binding, a->record PASS_LD);
  DEBUG(9, Sdprintf("First binding (%p): ", a->record);
	   PL_write_term(Serror, binding, 1200, PL_WRT_ATTVAR_WRITE);
	   Sdprintf("\n"));
  _PL_get_arg(1, binding, var_term);
  PL_unify(bindings, var_term);
  _PL_get_arg(2, binding, tmp);
  PL_cons_list(list, tmp, list);

  next = a->next;
  freeAssoc(prev, a PASS_LD);  

  if ( next != NULL )
  { for( a = next, next = a->next; next; a = next, next = a->next )
    { if ( !a->record )
	break;

      if ( !structuralEqualArg1OfRecord(var_term, a->record PASS_LD) == 0 )
      { prev = a;
	continue;
      }

      copyRecordToGlobal(binding, a->record PASS_LD);
      _PL_get_arg(1, binding, tmp);
      PL_unify(tmp, bindings);
      _PL_get_arg(2, binding, tmp);
      PL_cons_list(list, tmp, list);
      SECURE(checkData(valTermRef(list)));
      freeAssoc(prev, a PASS_LD);
    }
  }

  SECURE(checkData(valTermRef(var_term)));

  return PL_unify(bag, list);
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
An exception was generated during  the   execution  of  the generator of
findall/3, bagof/3 or setof/3. Reclaim  all   records  and  re-throw the
exception.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static void
discardBag(ARG1_LD)
{ Assoc a, next;

  for( a=alist; a; a = next )
  { if ( a->record )
    { DEBUG(1, Sdprintf("\tFree %p\n", a->record));
      freeRecord(a->record);
      next = a->next;
    } else
    { alist = a->next;
      next = NULL;
    }

    freeHeap(a, sizeof(*a));
  }
}


static
PRED_IMPL("$discard_bag", 0, discard_bag, 0)
{ PRED_LD

  discardBag(PASS_LD1);

  succeed;
}


		 /*******************************
		 *	NEW IMPLEMENTATION	*
		 *******************************/

#define BAG_MAGIC	0x74eb8afc
#define CHUNK_SIZE 	256

typedef struct achunk
{ struct achunk *next;
  int		used;
  struct assoc	assocs[CHUNK_SIZE];
} *AChunk;

typedef struct bag
{ int	magic;
  Assoc	head;
  Assoc	tail;
  int	size;
  int	gsize;
  AChunk chunks;
  struct achunk chunk1;
} *Bag;


static
PRED_IMPL("$create_bag", 1, create_bag, 0)
{ PRED_LD
  Bag b = allocHeap(sizeof(*b));

  b->magic	  = BAG_MAGIC;
  b->head	  = NULL;
  b->tail	  = NULL;
  b->size	  = 0;
  b->gsize	  = 0;
  b->chunks	  = &b->chunk1;
  b->chunks->used = 0;
  b->chunks->next = NULL;

  return PL_unify_pointer(A1, b);
}


static void
destroy_bag(Bag b ARG_LD)
{ Assoc a;
  AChunk c, next;

  for(a=b->head; a; a=a->next)
    freeRecord(a->record);

  for(c=b->chunks; c != &b->chunk1; c = next)
  { next = c->next;
    freeHeap(c, sizeof(*c));
  }
  
  b->magic = 0;
  freeHeap(b, sizeof(*b));
}


static Assoc
allocAssocBag(Bag b ARG_LD)
{ AChunk c;

  c = b->chunks;
  if ( c->used < CHUNK_SIZE )
    return &c->assocs[c->used++];

  c = allocHeap(sizeof(*c));
  c->used = 1;
  c->next = b->chunks;
  b->chunks = c;

  return c->assocs;
}


static int
get_bag(term_t t, Bag *b ARG_LD)
{ if ( !PL_get_pointer(t, (void**)b) || (*b)->magic != BAG_MAGIC )
    return PL_error(NULL, 0, NULL, ERR_TYPE, PL_new_atom("bag"), t);

  succeed;
}


static
PRED_IMPL("$append_bag", 2, append_bag, 0)
{ PRED_LD
  Bag b;
  Assoc a;

  if ( !get_bag(A1, &b PASS_LD) )
    fail;

  a = allocAssocBag(b PASS_LD);
  a->record = compileTermToHeap(A2, 0);
  a->next   = NULL;
  if ( b->tail )
  { b->tail->next = a;
    b->tail = a;
  } else
  { b->head = b->tail = a;
  }
  b->size++;
  b->gsize += a->record->gsize;

  succeed;
}


static
PRED_IMPL("$bag_to_list", 2, bag_to_list, 0)
{ PRED_LD
  Bag b;
  term_t tmp = PL_new_term_ref();
  Word base, next = NULL, end;
  int cells;
  Assoc a;

  if ( !get_bag(A1, &b PASS_LD) )
    fail;

  if ( b->size == 0 )
  { destroy_bag(b PASS_LD);
    return PL_unify_nil(A2);
  }

  cells = b->gsize + b->size*3 + 1;
  requireStack(global, cells*sizeof(word));
  end = gTop + cells;
  next = base = gTop++;

  for(a=b->head; a; a=a->next)
  { copyRecordToGlobal(tmp, a->record PASS_LD);
    *next = consPtr(gTop, TAG_COMPOUND|STG_GLOBAL);
    gTop[0] = FUNCTOR_dot2;
    gTop[1] = *valTermRef(tmp);
    gTop[2] = ATOM_nil;
    next = &gTop[2];
    gTop += 3;
  }
  assert(end == gTop);

  destroy_bag(b PASS_LD);

  return unify_ptrs(valTermRef(A2), base PASS_LD);
}


static
PRED_IMPL("$destroy_bag", 1, destroy_bag, 0)
{ PRED_LD
  Bag b;

  if ( !get_bag(A1, &b PASS_LD) )
    fail;
  
  destroy_bag(b PASS_LD);

  succeed;
}



		 /*******************************
		 *      PUBLISH PREDICATES	*
		 *******************************/

BeginPredDefs(bag)
  PRED_DEF("$record_bag", 1, record_bag, 0)
  PRED_DEF("$collect_bag", 2, collect_bag, 0)
  PRED_DEF("$discard_bag", 0, discard_bag, 0)

  PRED_DEF("$create_bag", 1, create_bag, 0)
  PRED_DEF("$append_bag", 2, append_bag, 0)
  PRED_DEF("$bag_to_list", 2, bag_to_list, 0)
  PRED_DEF("$destroy_bag", 1, destroy_bag, 0)
EndPredDefs
