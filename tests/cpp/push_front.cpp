// push_front: prepend a freshly allocated node (L-ptr third shape,
// allocating leg). Discipline: `Node` is a two-field struct
// (`int val`, `Node *next`); the entry takes the head pointer
// (caller-owned, possibly null) and the payload, allocates one
// node with `malloc`, and returns the new head. The single
// pointer param needs no `__restrict__` (single-pointer
// exemption); the fresh node escapes only via the return,
// disjoint by construction (allocator counter). Allocation
// failure is loud, not branched: a null `malloc` result
// aborts on the first dereference (`nd->val` misses loudly),
// exactly the L-ptr miss discipline — the corpus carries no
// explicit null check. Cycles are out of scope (the contract
// assumes an acyclic input chain).
// Spec: on exit the returned chain is `val` consed onto the
// input chain with all old payloads untouched.
#include <stdlib.h>

struct Node {
  int val;
  Node *next;
};

Node *push_front(Node *head, int val) {
  Node *nd = (Node *)malloc(sizeof(Node));
  nd->val = val;
  nd->next = head;
  return nd;
}
