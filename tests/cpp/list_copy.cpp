// list_copy: deep-copy the chain (P1 fourth shape, allocation
// inside a traversal loop). Discipline: `Node` is a two-field
// struct (`int val`, `Node *next`); the entry takes the head
// pointer (caller-owned, possibly null) and chases with a
// single cursor, `malloc`-ing one fresh cell per node,
// copying the payload, clearing the fresh link, and
// appending to the new tail (head-case vs interior-case on
// the new tail). Returns the new head (`nullptr` on empty
// input). The single pointer param needs no `__restrict__`
// (single-pointer exemption). The input chain is never
// written — only the fresh cells are stored. Faults are
// loud, not branched: allocation failure, dereferencing a
// null, missing, or dead cell aborts in the model (`memAlloc`
// is infallible in the current runtime; `memLoad` miss/tag
// checks), exactly the L-ptr miss discipline — the corpus
// carries no explicit checks. Cycles are out of scope (the
// contract assumes an acyclic input chain). Spec: on exit
// the returned chain holds the input payloads in order, every
// returned cell is fresh (pairwise distinct and disjoint from
// the input), the input chain is untouched.
#include <stdlib.h>

struct Node {
  int val;
  Node *next;
};

Node *list_copy(Node *head) {
  Node *new_head = nullptr;
  Node *tail = nullptr;
  Node *cur = head;
  while (cur != nullptr) {
    Node *nd = (Node *)malloc(sizeof(Node));
    nd->val = cur->val;
    nd->next = nullptr;
    if (tail == nullptr) {
      new_head = nd;
    } else {
      tail->next = nd;
    }
    tail = nd;
    cur = cur->next;
  }
  return new_head;
}
