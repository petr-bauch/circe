// list_merge: splice two ascending chains into one ascending chain
// (P1 first multi-input traversal, destructive merge reusing the
// head-seed + tail-swing structure of the copy kit). Discipline:
// `Node` is a two-field struct (`int val`, `Node *next`); the
// entry takes two head pointers (both caller-owned, possibly
// null) and returns the merged head (`a`/`b` remainder for an
// empty other side, null for both empty). Both params carry
// `__restrict__` (two live pointers can always alias, so
// uniqueness is claimed in the text and corroborated by a
// `noalias` oracle verdict; the single-pointer exemption does
// not apply). The merge is destructive: nodes are relinked, no
// `malloc`/`free` by design; `new` is not used. The tie rule is
// take-from-`a` on `a->val <= b->val` (stable). Faults are
// loud, not branched: dereferencing a null, missing, or dead
// cell aborts in the model (`memLoad` miss/tag/liveness
// checks), exactly the L-ptr miss discipline — the corpus
// carries no explicit checks. Cycles are out of scope (the
// contract assumes two acyclic, pairwise-disjoint input
// chains). Spec: on sorted inputs the result is the sorted
// chain holding exactly the multiset union of the payloads.
struct Node {
  int val;
  Node *next;
};

Node *list_merge(Node * __restrict__ a, Node * __restrict__ b) {
  if (a == nullptr) {
    return b;
  }
  if (b == nullptr) {
    return a;
  }
  Node *head;
  Node *tail;
  if (a->val <= b->val) {
    head = a;
    a = a->next;
  } else {
    head = b;
    b = b->next;
  }
  tail = head;
  while (a != nullptr && b != nullptr) {
    if (a->val <= b->val) {
      tail->next = a;
      a = a->next;
    } else {
      tail->next = b;
      b = b->next;
    }
    tail = tail->next;
  }
  if (a != nullptr) {
    tail->next = a;
  } else {
    tail->next = b;
  }
  return head;
}
