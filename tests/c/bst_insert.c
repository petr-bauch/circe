// bst_insert: iterative BST insert with per-element `malloc`
// (P1 tree-kit second shape, write leg over the chase
// discipline). Discipline: `Node` is a three-field struct
// (`int key`, `Node *left`, `Node *right`); the entry takes the
// root pointer (caller-owned, possibly null) and the key, and
// returns the (possibly new) root — the tree gains exactly one
// node holding the key (set semantics: a duplicate key is a
// no-op that allocates nothing). Descent mirrors
// `bst_search` (signed `<` picks the side); the attach writes
// the empty child link with a fresh 3-word node (`key`, null
// link, null link) obtained from a single `malloc`. Only one
// allocation happens, and only on the attach path. Faults are
// loud as usual (null/missing/dead reads, short writes);
// cycles and a broken BST invariant are out of contract (the
// proof assumes an acyclic BST input). Spec: on exit the
// flatten is the sorted insertion of the key and the BST
// invariant is preserved; the old root is returned unchanged
// on duplicate.
#include <stddef.h>
#include <stdlib.h>

struct Node {
  int key;
  struct Node *left;
  struct Node *right;
};

struct Node *bst_insert(struct Node *root, int key) {
  struct Node *parent = NULL;
  struct Node *cur = root;
  int went_left = 0;
  while (cur != NULL) {
    if (key == cur->key) {
      return root;
    } else if (key < cur->key) {
      parent = cur;
      cur = cur->left;
      went_left = 1;
    } else {
      parent = cur;
      cur = cur->right;
      went_left = 0;
    }
  }
  struct Node *nd = (struct Node *)malloc(sizeof(struct Node));
  nd->key = key;
  nd->left = NULL;
  nd->right = NULL;
  if (parent == NULL) {
    return nd;
  } else if (went_left) {
    parent->left = nd;
  } else {
    parent->right = nd;
  }
  return root;
}
