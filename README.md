## Ramsey's theorem in Type Theory

### Copyright

```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*                                                            *)
(*                 [*] Affiliation LORIA -- CNRS              *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)
```

### What is this repository for? ###

* This repository is a Coq implementation and total correctness
  proof of L. Paulson If-Then-Else normalisation which is a nested
  recursive algorithm with a complicated scheme.

```ocaml
type Ω = α | ω of Ω * Ω * Ω

let rec nm e = match e with
  | α                => α
  | ω (α,y,z)        => ω (α,nm y,nm z)
  | ω (ω(a,b,c),y,z) => nm (ω (a,nm (ω (b,y,z)),nm (ω (c,y,z)))
```


* The paper [Simulating Induction-Recursion for Partials Algorithms](http://www.loria.fr/~larchey/papers/TYPES_2018_paper_19.pdf)
  submitted to [TYPES 2018](http://w3.math.uminho.pt/types2018) describes the technique. 

### What does it contains

### How do I set it up? ###

* This should compile with Coq 8.6+ with `cd src; make af.vo hwf.vo`.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)

