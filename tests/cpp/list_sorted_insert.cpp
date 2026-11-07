// list_sorted_insert: insert a fresh node into an ascending chain
// (P1 first ordered shape, find + link-swing composition reusing
// the query and writer kits). Discipline: `Node` is a two-field
// struct (`int val`, `Node *next`); the entry takes the head
// pointer (caller-owned, possibly null) and the payload, chases
// with a prev/cur pair while `cur->val <= val` (upper-bound rule:
// the new node lands after existing equals), swings the links of
// a single `malloc`-ed node, and returns the (possibly new) head.
// The single pointer param needs no `__restrict__`
// (single-pointer exemption). No `free` by design; `new` is not
// used (the P1 corpus forbids `_Znwm`: the fresh node comes from
// `(Node *)malloc(sizeof(Node))`, the P1-copy per-node kit).
// Faults are loud, not branched: dereferencing a null, missing,
// or dead cell aborts in the model (`memLoad` miss/tag/liveness
// checks), exactly the L-ptr miss discipline — the corpus carries
// no explicit checks. Cycles are out of scope (the contract
// assumes an acyclic input chain). Spec: on a sorted input the
// result is the sorted chain with the payload inserted.
#include <cstdlib>
struct Node {
  int val;
  Node *next;
};

Node *list_sorted_insert(Node *head, int val) {
  Node *nd = (Node *)malloc(sizeof(Node));
  nd->val = val;
  Node *prev = nullptr;
  Node *cur = head;
  while (cur != nullptr && cur->val <= val) {
    prev = cur;
    cur = cur->next;
  }
  nd->next = cur;
  if (prev == nullptr) {
    head = nd;
  } else {
    prev->next = nd;
  }
  return head;
}
