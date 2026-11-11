// bst_search: iterative BST membership query (P1 tree-kit first
// shape, read-only descent reusing the chase discipline).
// Discipline: `Node` is a three-field struct (`int key`,
// `Node *left`, `Node *right`); the entry takes the root pointer
// (caller-owned, possibly null) and the key, descends with a
// single cursor comparing against each node's key, and returns
// 1 on the first match, 0 on miss (or empty input). The single
// pointer param needs no `__restrict__` (single-pointer
// exemption). The function is read-only by design: no stores
// to the tree, no `malloc`, no `free` — the loop guard, not a
// branch, covers misses. Faults are loud, not branched:
// dereferencing a null, missing, or dead cell aborts in the
// model (`memLoad` miss/tag/liveness checks), exactly the L-ptr
// miss discipline — the corpus carries no explicit checks.
// Cycles are out of scope (the contract assumes an acyclic
// input chain). The descent is correct only under the BST
// invariant (left subtree keys < node key < right subtree
// keys); the invariant is a proof hypothesis, not a runtime
// check. Spec: on exit the return is 1 iff the key occurs in
// the tree; memory is untouched.
#include <stddef.h>

struct Node {
  int key;
  struct Node *left;
  struct Node *right;
};

int bst_search(struct Node *root, int key) {
  struct Node *cur = root;
  while (cur != NULL) {
    if (key == cur->key) {
      return 1;
    } else if (key < cur->key) {
      cur = cur->left;
    } else {
      cur = cur->right;
    }
  }
  return 0;
}
