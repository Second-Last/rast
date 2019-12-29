alternate.ss -- alternating between input streams; time, not work

append-bug.ss
append-implicit.ss -- append, stack_list; no idx, no time, no work
append-qrecon.ss -- append, reverse, stack_list; idx length, no work
append-time.ss -- append with arrival rates r; idx length and rate time, no work
append-wrecon.ss -- append with work p, rev, stack_list, work=send, syntax=implicit
append.ss -- append with fixed work, work=send, syntax=explicit

arith.ss -- binary arithmetic: zero, succ, drop, dup, times, inc, dec, beginning of filter

fold.ss -- recursive fold over lists, time=recvsend, syntax=explicit

int-idx-refl.ss (fails) -- integers as pairs of naturals, integer counter, type equality with reflexivity only
int-idx-subsume.ss (fails) -- integers as pairs of naturals, integer counter, type equality with subsumption only
int-idx.ss -- integers as pairs of naturals, integer counter; work=none, syntax=implicit
int-idx2.ss -- as int-idx2, --equality=refl, overcoming incompleteness with explicit coercion

linlam-bug.ss
linlam-idx.ss -- linear lambda-calculus, indexed as value/expression; work=none, syntax=implicit
              -- example of reconstructing missing branches
linlam-size.ss -- linear lambda-calculus indexed by size; work=none, syntax=implicit
               -- requires quantifiers
linlam-sub.ss  -- linear lambda-calculus, separating values and expressions, no idx
linlam.ss     -- linear lambda-calculus, no idx

list-quant.ss -- length-indexed lists: fold,map,rev,split,head,insert,partition,forall,exists,equal,merge
              -- no work, some fakes

parity.ss -- tree parity, with time

poly-append.ss -- polymorphic(?) append
poly-queue.ss -- linear work queue, syntax=explicit
queue.ss -- no-element fake queue, syntax = explicit 
queues-quant.ss -- incomplete queues

primes-idx.ss -- prime sieve implementation, work=none, idx on values and length
primes.ss -- prime sieve (no indices)

scan.ss -- in progress

seg-wrecon.ss -- list segments, work=send, syntax=implicit; should rewrite (see seg-work.ss)
seg-work.ss -- list segments, work=send, with quantifiers (as they should be)
seg.ss -- list segments, with idx but no work

stacks-quant.ss (does not compile) -- stack-based evaluation, with idx,

trie-idx-explicit-alpha.ss
trie-idx-explicit.ss
trie-idx-explicit2.ss
trie-idx-implicit.ss -- tries over binary numbers, work=none
trie-idx-recon.ss (obsolete)
trie-idx-work-fail.ss
trie-idx-work-unique.ss 
trie-idx-work.ss -- tries over binary numbers (including bin, ctr), work=send, syntax=implicit
trie-idx.ss (obsolete)
trie-quant-work.ss (obsolete)
trie-quant.ss (obsolete)
trie.ss -- tries over binary numbers, no idx or work
