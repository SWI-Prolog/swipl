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

typedef struct assoc
{ Record record;
  struct assoc *next;
} *Assoc;

static Word assoc_to_list(Assoc a, int size, int gsize ARG_LD);


		 /*******************************
		 *	 BAGOF/SETOF BAGS	*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Bagof support. For bagof/3 and setof/3 we maintain an AVL tree of values
for the free-variable template.  


- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


#include "pl-avl.h"

typedef struct bindnode
{ Record	record;			/* first binding */
  term_t	term;			/* As term (for search) */
  int		size;			/* # values on this binding */
  int		gsize;			/* Required global stack for list */
  Assoc		head;			/* solution list */
  Assoc		tail;
} bindnode;


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
compare_bindnodes() assumes the left-side is the   node that is searched
or inserted, while the right node is   already in the tree. Therefore we
use the term of the left, and the record of the right node.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static int
compare_bindnodes(void *l, void *r, NODE type)
{ GET_LD;
  bindnode *ln = l;
  bindnode *rn = r;

  return structuralEqualArg1OfRecord(ln->term, rn->record PASS_LD);
}


static void
free_assoc_list(Assoc a)
{ GET_LD
  Assoc next;

  for(; a; a=next)
  { next = a->next;
    freeRecord(a->record);
    freeHeap(a, sizeof(*a));
  }
}


static void
destroy_bindnode(void *client_data, void *ptr)
{ bindnode *node = ptr;

  free_assoc_list(node->head);
}



static
PRED_IMPL("$create_bagof", 1, create_bagof, 0)
{ PRED_LD
  avl_tree *t = allocHeap(sizeof(*t));

  avlinit(t,
	  NULL,				/* client data */
	  sizeof(bindnode),		/* item size */
	  compare_bindnodes,		/* compare nodes */
	  NULL,				/* destroy node */
	  NULL, NULL);			/* alloc/free (TBD: pool) */

  return PL_unify_pointer(A1, t);
}


static int
get_bagof(term_t t, avl_tree **b ARG_LD)
{ if ( !PL_get_pointer(t, (void**)b) )
    return PL_error(NULL, 0, NULL, ERR_TYPE, PL_new_atom("bag"), t);

  succeed;
}


static
PRED_IMPL("$destroy_bagof", 1, destroy_bagof, 0)
{ PRED_LD
  avl_tree *tree;

  if ( !get_bagof(A1, &tree PASS_LD) )
    fail;
  
  avlfree(tree);
  freeHeap(tree, sizeof(*tree));

  succeed;
}


static
PRED_IMPL("$insert_bagof", 2, insert_bagof, 0)
{ PRED_LD
  avl_tree *tree;
  bindnode node, *data;
  Assoc a;
  term_t binding = A2;			/* v(...)-Gen */
  term_t vars = PL_new_term_ref();	/* v(...) */

  if ( !get_bagof(A1, &tree PASS_LD) )
    fail;

  if ( !PL_get_arg(1, binding, vars) )
    fail;

  node.record = compileTermToHeap(binding, 0);
  node.term   = vars;

  a = allocHeap(sizeof(*a));
  a->record  = node.record;
  a->next    = NULL;

  if ( (data = avlfind(tree, &node)) )
  { data->size++;
    data->gsize += node.record->gsize;
    data->tail->next = a;
    data->tail = a;
  } else
  { node.size  = 1;
    node.gsize = node.record->gsize;
    node.head  = a;
    node.tail  = a;
    data = avlins(tree, &node);
  }

  succeed;
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
$collect_bagof(+Handle, +Vars, -Bag)

vars: v(....) term.  All arguments are variables.

restore_bindings() gets the variable template and   the  list. Note that
the list was created using assoc_to_list()   and contains no references.
It contains cells v(...)-Binding. Our task   is  to restore the variable
bindings by unifying vars  with  the  v(...)   term  of  each  cell  and
destructively rewrite the list value to   contain Binding instead of the
whole term. I guess we can optimize  the   unify  a bit, but that is for
later.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

static void
restore_bindings(Word vars, Word list ARG_LD)
{ while(isList(*list))
  { Word head = argTermP(*list, 0);
    Word arg1 = argTermP(*head, 0);
    if ( !unify_ptrs(vars, arg1 PASS_LD) )
      assert(0);
    *head = linkVal(arg1+1);

    list = head+1;
  }

  assert(isNil(*list));
}


static
PRED_IMPL("$collect_bagof", 3, collect_bagof, PL_FA_NONDETERMINISTIC)
{ PRED_LD
  avl_tree *tree;

  switch( CTX_CNTRL )
  { case FRG_FIRST_CALL:
      if ( !get_bagof(A1, &tree PASS_LD) )
	fail;
      goto next;
    case FRG_REDO:
    { bindnode node;
      fid_t fid;

      tree = CTX_PTR;
    next:
      fid = PL_open_foreign_frame();
      while ( avldelmin(tree, &node) )
      { Word list = assoc_to_list(node.head, node.size, node.gsize PASS_LD);

	free_assoc_list(node.head);
	restore_bindings(valTermRef(A2), list PASS_LD);
	if ( unify_ptrs(valTermRef(A3), list PASS_LD) )
	{ PL_close_foreign_frame(fid);
	  if ( avlcount(tree) == 0 )
	  { freeHeap(tree, sizeof(*tree));
	    succeed;
	  } else
	  { ForeignRedoPtr(tree);
	  }
	}

	PL_rewind_foreign_frame(fid);
      }
      freeHeap(tree, sizeof(*tree));
      fail;
    }
    case FRG_CUTTED:
      tree = CTX_PTR;
      tree->destroy = destroy_bindnode;
      avlfree(tree);
      freeHeap(tree, sizeof(*tree));
      succeed;
    default:
      assert(0);
      fail;
  }
}



		 /*******************************
		 *	   FINDALL BAGS		*
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


static Word
assoc_to_list(Assoc a, int size, int gsize ARG_LD)
{ term_t tmp = PL_new_term_ref();
  Word base, next = NULL, end;
  int cells;

  cells = gsize + size*3 + 1;
  requireStack(global, cells*sizeof(word));
  end = gTop + cells;
  next = base = gTop++;

  for(; a; a=a->next)
  { copyRecordToGlobal(tmp, a->record PASS_LD);
    *next = consPtr(gTop, TAG_COMPOUND|STG_GLOBAL);
    gTop[0] = FUNCTOR_dot2;
    gTop[1] = *valTermRef(tmp);
    gTop[2] = ATOM_nil;
    next = &gTop[2];
    gTop += 3;
  }
  assert(end == gTop);

  return base;
}


static
PRED_IMPL("$bag_to_list", 2, bag_to_list, 0)
{ PRED_LD
  Bag b;
  Word list;

  if ( !get_bag(A1, &b PASS_LD) )
    fail;

  if ( b->size == 0 )
  { destroy_bag(b PASS_LD);
    return PL_unify_nil(A2);
  }

  list = assoc_to_list(b->head, b->size, b->gsize PASS_LD);
  destroy_bag(b PASS_LD);

  return unify_ptrs(valTermRef(A2), list PASS_LD);
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
					/* bagof */
  PRED_DEF("$create_bagof", 1, create_bagof, 0)
  PRED_DEF("$destroy_bagof", 1, destroy_bagof, 0)
  PRED_DEF("$insert_bagof", 2, insert_bagof, 0)
  PRED_DEF("$collect_bagof", 3, collect_bagof, PL_FA_NONDETERMINISTIC)

					/* findall */
  PRED_DEF("$create_bag", 1, create_bag, 0)
  PRED_DEF("$append_bag", 2, append_bag, 0)
  PRED_DEF("$bag_to_list", 2, bag_to_list, 0)
  PRED_DEF("$destroy_bag", 1, destroy_bag, 0)
EndPredDefs
