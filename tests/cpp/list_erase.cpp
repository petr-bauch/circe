// list_erase: unlink the first matching node and free it (P1 second
// shape, deallocating leg). Discipline: `Node` is a two-field
// struct (`int val`, `Node *next`); the entry takes the head
// pointer (caller-owned, possibly null) and the payload, chases
// with a trailing pointer, unlinks the first node whose payload
// matches (`head` case vs interior case), frees exactly that cell,
// and returns the (possibly new) head. The single pointer param
// needs no `__restrict__` (single-pointer exemption). Miss legs
// are silent by design: no match (or empty input) returns the
// head untouched with no `free` — the loop guard, not a branch,
// covers them. Faults are loud, not branched: freeing a null,
// missing, or already-freed cell aborts in the model
// (`memFree` miss/tag/liveness checks), exactly the L-ptr miss
// discipline — the corpus carries no explicit checks. Cycles are
// out of scope (the contract assumes an acyclic input chain).
// Spec: on exit the returned chain is the input chain minus its
// first matching payload, the freed cell is dead (live flag
// cleared, contents kept but unusable — any later dereference
// misses loudly), all other payloads untouched.
#include <stdlib.h>

struct Node {
  int val;
  Node *next;
};

Node *list_erase(Node *head, int val) {
  Node *prev = nullptr;
  Node *cur = head;
  while (cur != nullptr) {
    if (cur->val == val) {
      if (prev == nullptr) {
        head = cur->next;
      } else {
        prev->next = cur->next;
      }
      free(cur);
      return head;
    }
    prev = cur;
    cur = cur->next;
  }
  return head;
}
