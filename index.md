Welcome to the *Principia* Rewrite project website!

* TOC
{:toc}

# What is the project? What are you trying to do?
What we are doing is best explained by a picture:
![*2.37: the original *Principia* proof, the `Coq` proof, and the rewritten proof side-by-side-by-side](2.37sidebysidebysideArrows.png)
We are taking the original *Principia* proof on the left, which is really a proof sketch omitting a lot of steps, and filling out the missing steps. For this we are using the interactive theorem prover `Coq` to ensure each proof step is a valid step according to *Principia*'s axioms and that no steps are skipped, even by accident. Finally, we are using the `Coq` encoding to typeset the full, gapless proof as it would appear in *Principia*'s notation.

# Why are you doing all *that*?
Because it is fun. We also want academics and the public to engage more with Whitehead and Russell's landmark three-volume work on logic and the foundations of mathematics. The project aims to facilitate that by producing a scholarly edition of *Principia* that is pleasingly typeset and searchable.

# Are those the *only* reasons?
No. We also think that computational methods, and especially interactive theorem provers that help one rationally reconstruct arguments, can be of some use to historians of philosophy. We aim to prove this - that computational tools can augment traditional methods in history of philosophy - by giving an example.

# Are there any *other* reasons?
Yes. *Principia* has been criticized by famous logicians like Kurt Gödel as being a "step backwards" from Frege and for being generally sloppy. We think that some of these charges are definitely overstated, and we want to contribute to the scholarly literature by rebutting some of them.

# Is that *all* you are doing?
No. Because we want to typeset *Principia* pleasingly, we are also creating a `LaTeX` package for typesetting *Principia*'s idiosyncratic notation, which is no longer included in standard typesetting engines. We have already published a `principia` package on `CTAN` that covers all notations occurring in Volume I of *Principia*. We will extend it to Volumes II and III in due course.

# Is there anything *else* you are doing?
We also want to create a subway-style map of *Principia* that allows one to click a theorem and see where it is used, what is used to prove it, and so on. One will be able to survey the text of *Principia* for the first time. So we are also marking up *Principia*'s theorems and proof sketches, and the `Coq` ones, in `XML`. Then we will use `Python` to create the interactive maps.

# That sounds like a lot. What is your timeline?
It is definitely a lot. We would be very happy to get Volume I done by 2025, which will be exactly one hundred years since *Principia*'s second edition was published. So we might give a rough estimate of one volume every five years.

# Who is doing tihs?
The principal investigator is your resident logical atomist, [Landon D. C. Elkind](https://landondcelkind.com) ([@LogicalAtomist](https://twitter.com/LogicalAtomist)), who is affiliated with the Department of Philosophy at the University of Alberta. I began and am currently undertaking this project with the suppoert of an [Izaak Walton Killam Postdoctoral Fellowship](https://www.ualberta.ca/graduate-studies/about/celebrating-our-killam-laureates/2020-izaak-walton-killam-postdoctoral.html).

# Updates
The *Principia* Rewrite project has a [GitHub repository](https://github.com/LogicalAtomist/principia). Regular updates and the source code are made available there, whereas project milestones will be announced below.

## February 15, 2021
The project has formally verified *Principia*'s propositional logic proof sketches - for all 189 theorems in \*1-to-\*5 - for the very first time. This improves significantly on the earlier computer verification work of Allen Newell *et al*., Hao Wang, and Daniel O'Leary. In all three cases, either some theorems were not verified or their proofs were not reconstructed according to *Principia*'s proof sketches. Our project in contrast reconstructs all the proofs in a way that is faithful to the text: each completion of *Principia*'s proof in `Coq` make use of every theorem cited in *Principia*'s proof sketch.

# Digital publications
As of February 15, 2021, the *Principia* Rewrite project has also produced:

1. a `LaTeX` package, [`principia`](https://ctan.org/pkg/principia), for typesetting any symbol in *Principia*'s Volume I
2. a `Coq` file of *Principia*'s propositional logic (\*1-\*5), running about [4,700 lines of code](https://github.com/LogicalAtomist/principia/blob/master/PL.v) / [113 pages](https://github.com/LogicalAtomist/principia/blob/master/PL.pdf)
3. a pleasingly typeset edition of *Principia*'s first 131 pages in `LaTeX`, going from its introduction through the end of its propositional logic (up to \*5).

There are further developments to come: a high priority for the project is to build a map of the first five chapters ("starred numbers") of *Principia* - because maps are fun and cool, besides being informative when done well.

# Contact
If you have any questions, criticisms, or thoughts related to the *Principia* Rewrite project, write to `elkind at ualberta dot ca`.

![*Principia* & `Coq` side-by-side](PM2.14-2.15.png)
![Sample page of *Principia* digitized with `LaTeX` using the `principia` package](SamplePMalphabeticallistofprops.png)
