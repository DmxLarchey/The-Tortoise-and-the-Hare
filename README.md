# The Tortoise and the Hare in Coq

        (**************************************************************)
        (*   Copyright Dominique Larchey-Wendling [*]                 *)
        (*                                                            *)
        (*                             [*] Affiliation LORIA -- CNRS  *)
        (**************************************************************)
        (*      This file is distributed under the terms of the       *)
        (*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
        (**************************************************************)

## What is this repository for

* This repository contains the Coq source code that comes as a companion to the paper [*Proof Pearl: Constructive Extraction of Cycle Finding Algorithms*](http://www.loria.fr/~larchey/papers/ITP_2018_paper_16.pdf) by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey), currently submitted to ITP 2018.

## How do I set it up

* Use Coq 8.6 (preferably). The code also compiles with Coq 8.5pl[23]. But **not under Coq 8.7** (see below). 
* To compile, type `make all`. Then one can visit the individual proof files `*.v`
* Beware that `Extraction` will fail with Coq 8.7+ because `Require Extraction` should be included before extraction takes place. This is an unfortunate incompatibility introduced in Coq 8.7. 
* If using Coq 8.7 is nonetheless important, the rest of the code should work ok, so simply add `Require Extraction` where it is needed.
