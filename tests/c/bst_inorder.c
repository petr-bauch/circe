// bst_inorder: iterative inorder traversal (P1 tree-kit third
// shape, explicit-stack flatten over the chase discipline).
// Discipline: `Node` is a three-field struct (`int key`,
// `Node *left`, `Node *right`); the entry takes the root pointer
// (caller-owned, possibly null), a caller-owned output buffer
// `out` with capacity `cap`, and writes the keys in inorder,
// returning the count. The traversal uses an explicit local
// stack (no recursion): push the left spine, pop, emit, swing
// right. The stack holds at most 64 ancestors (deeper trees
// are out of contract, a proof hypothesis like the BST
// invariant); filling the output (`n >= cap`) or the stack is
// a loud `-1`, never a silent truncation. Faults are loud as
// usual (null/missing/dead reads); cycles are out of contract.
// Spec: on exit `out[0..n]` is the inorder key sequence and
// memory is untouched (read-only apart from `out`).
#include <stddef.h>

struct Node {
  int key;
  struct Node *left;
  struct Node *right;
};

int bst_inorder(struct Node *root, int *out, int cap) {
  struct Node *st[64];
  int top = 0;
  struct Node *cur = root;
  int n = 0;
  while (cur != NULL || top > 0) {
    while (cur != NULL) {
      if (top >= 64) {
        return -1;
      }
      st[top] = cur;
      top = top + 1;
      cur = cur->left;
    }
    top = top - 1;
    cur = st[top];
    if (n >= cap) {
      return -1;
    }
    out[n] = cur->key;
    n = n + 1;
    cur = cur->right;
  }
  return n;
}
