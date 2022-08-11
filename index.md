Welcome to the *Principia* Rewrite project website! To receive updates about project milestones, you can subscribe to our email list here: https://lists.wku.edu/mailman/listinfo/principia.rewrite.

# Table of contents

* TOC
{:toc}

# What is the project? What are you trying to do?
What we are doing is best explained by a picture:
![*2.37: the original *Principia* proof, the `Coq` proof, and the rewritten proof side-by-side-by-side](2.37sidebysidebysideArrows.png)
We are taking Whitehead and Russell's original *Principia* proof on the left, which is really a proof sketch omitting a lot of steps, and filling out the missing steps. For this we are using the interactive theorem prover `Coq` to ensure each proof step is a valid step according to *Principia*'s axioms and that no steps are skipped, even by accident. Finally, we are using the `Coq` encoding to typeset the full, gapless proof as it would appear in *Principia*'s notation.

# Why are you doing all *that*?
Because it is fun. We also want academics and the public to engage more with Whitehead and Russell's landmark three-volume work on logic and the foundations of mathematics. The project aims to facilitate that by producing a scholarly edition of *Principia* that is pleasingly typeset and searchable.

# Are those the *only* reasons?
No. We also think that computational methods, and especially interactive theorem provers that help one rationally reconstruct arguments, can be of some use to historians of philosophy. We aim to prove this - that computational tools can augment traditional methods in history of philosophy - by giving an example.

# Are there any *other* reasons?
Yes. *Principia* has no editorial apparatus: there is no index of where starred numbers are used, no easily surveyable table indicating, for each starred number, what is cited in its proof. There is no dependency diagram indicating which chapters and sections depend on which other parts of *Principia*. So we want to illuminate the *structure* of the text by indicating these logical connections between different subject-matter areas. This construction builds on earlier scholarship: Sebastien Gandon, for example, argued that *Principia* does not embrace an arithmetization of mathematics (reducing mathematics to arithmetic, then reducing arithmetic to logic). Rather, different branches of mathematics are reduced to different logical kinds of relation in partial logical independence of one another. Gandon's work convincingly shows this is how Whitehead and Russell proceeded; but the practical verification of Gandon's thesis requires a clear view of the text's logical dependency structure. This is one of the upshots of our work.

# Are there any other, *other* reasons?
Yes. In *Principia*'s Preface, Whitehead and Russell wrote:

>Detailed acknowledgments of obligations to previous writers have not very often been possible, as we have had to transform whatever we have borrowed, in order to adapt it to our system and our notation. Our chief obligations will be obvious to every reader who is familiar with the literature of the subject.

Given the developments in mathematics since *Principia* was published, *Principia*'s chief obligations are no longer obvious to readers familiar with the usual literature. Accordingly, we want to make perspicious and apparent to modern readers *Principia*'s intellectual ancestry (and debts). We will indicate the antecedents of *Principia*'s starred numbers in other texts (especially in contemperaneous nineteenth-and-twentieth-century mathematical works of Peano, Hausdorff, Frege, Cantor, Schroder, and Zermelo). The upshot will be a network mapping of the intellectual context for *Principia* that will be of use to historians of (late-ninteenth-century and early-twentieth-century) science.

# Is that *all* you are doing?
No. Because we want to typeset *Principia* pleasingly, we are also creating a `LaTeX` package for typesetting *Principia*'s idiosyncratic notation, which is no longer included in standard typesetting engines. We have already published an early version of the `principia` package on `CTAN` that covers many of the notations occurring in Volume I of *Principia*. We will publish an updated package that allows for reproducing the entirety of *Principia*'s notations in due course.

# Is there anything *else* you are doing?
We also want to create a subway-style map of *Principia* that allows one to click a theorem and see where it is used, what is used to prove it, and so on. One will be able to survey the text of *Principia* for the first time. So we are also marking up *Principia*'s theorems and proof sketches, and the `Coq` ones, in a `Neo4j` database. Then we will take the exported `JSON` file and use `Python` to enable user generation of various interactive maps and to export results of queries of the `Neo4j` database.

# That sounds like a lot. What is your timeline?
It is definitely a lot. We plan (and would be very happy) to get Volume I re-typeset and published with its new editorial apparatus by 2025, which will be exactly one hundred years since *Principia*'s second edition was published. The timeline for re-doing all three volumes and adding their editorial apparatuses is partly dependent on whether our grant applications are successful. And the computer-assisted rewriting side of the project will follow the re-typesetting of the original work (although progress has already begun on that side of things, too).

# Who is doing this?
There is a team of people involved in this project.

## Principal Investigator
The principal investigator is Western Kentucky University's resident logical atomist, [Landon D. C. Elkind](https://landonelkind.com) ([Assistant Professor of Philosophy](https://www.wku.edu/philosophy-religion/), [Department of Political Science](https://www.wku.edu/political-science/)). The project began on September 1st, 2020, and was first undertaken while Elkind was a Izaak Walton Killam Postdoctoral Fellow in the [Department of Philosophy](https://www.ualberta.ca/philosophy/index.html) at the University of Alberta.

## Advisory Board
- Rodrigo Ferreira ([Federal University of Rio Grande do Sul-Brazil](https://sites.google.com/view/rsferreira))
- Nicholas Griffin ([McMaster University](https://experts.mcmaster.ca/display/ngriffin))
- Brice Halimi ([Université de Paris](https://sites.google.com/view/brice-halimi))
- Peter Hylton ([University of Illinois-Chicago](https://phil.uic.edu/profiles/hylton-peter/) and [Boston University](https://www.bu.edu/philo/profile/peter-hylton/))
- Kevin Klement ([University of Massachusetts-Amherst](https://www.umass.edu/philosophy/member/kevin-klement))
- Gregory Landini ([University of Iowa](https://clas.uiowa.edu/philosophy/people/gregory-landini))
- James Levine ([Trinity College-Dublin](https://www.tcd.ie/research/profiles/?profile=jlevine))
- Albert Lewis ([Educational Advancement Foundation](https://www.neomon.us/))
- Bernard Linsky ([University of Alberta](https://sites.ualberta.ca/~blinsky/blinsky.html))
- Gülberk Koç Maclean ([Mount Royal University](https://www.mtroyal.ca/ProgramsCourses/FacultiesSchoolsCentres/Arts/Departments/Humanities/Faculty/GulberkKocMaclean.htm))
- Daniel O'Leary ([Ombu Enterprises, LLC](https://www.linkedin.com/in/dan-o-leary-78579111/))
- Anne-Francoise Schmid ([Institut National des Sciences Appliquees de Lyon](https://schmidannefrancoise.academia.edu/))
- Graham Stevens ([University of Manchester](https://www.research.manchester.ac.uk/portal/en/researchers/graham-stevens(007e6671-876a-4dee-b2df-e45bb74dc710).html))
- Russell Wahl ([Idaho State University](https://idahostate.academia.edu/RussellWahl))

*Note: this advisory board is for the new critical edition of Principia Mathematica edited by the principal investigator (under contract with Cambridge University Press), not necessarily for other components of the Principia Rewrite project, e.g., the use of interactive proof assistants to reconstruct the proofs in Principia.*

## Additional Team Members
- Guanda Yuan (University of Iowa, M.S. in Computer Science, 2021), Intern (2021-present)

# Updates
The *Principia* Rewrite project has a [GitHub repository](https://github.com/LogicalAtomist/principia). Regular updates and the source code are made available there. Project milestones will be announced below.

## December 1, 2021
Happy Hanukkah! We are happy to announce that Cambridge University Press has agreed to publish a critical edition of *Principia Mathematica*. This will be a beautifully typeset accurate edition that preserves the original work's notations and proofs. The new edition will also include some new editorial material, including tables showing everywhere a given starred number is used and every starred number cited in a given theorem's proof. There will also be contextualizing footnotes indicating antecedents of a given starred number or its proof in nineteenth-or-early-twentieth-century texts, which will make perspicuous the intellectual context for *Principia*.

We are also happy to announce that our project is growing! We have a new advisory board (see above) that will of course advise the editor on this project. And we also have our first intern with the project, Guanda Yuan, who will be helping us complete a *Principia* database in [Neo4j](https://www.neo4j.com). This database will be used to create the new editorial material, helping us map the dependencies and intellectual context for *Principia*'s Logicization of mathematics. Welcome, Guanda!

Finally, the typesetting of Volume I is about 38% complete (i.e. the informal introductions, the second edition material, and the entirety of Part I, §§A-B). We expect the entire Volume I to be completely typeset by the end of 2022. Stay tuned for more updates!

## May 1, 2021
Happy International Workers' Day! The source code for the verification of *Principia*'s propositional logic proof sketches in `Coq` has been updated again. Now all the proofs are *forward-directed* - steps in the proofs involve only transformations of premises - rather than *backward-directed* - steps in the proofs do not involve transformations of the theorem (or proof goal). Also, the conjunction Ltac `Conj` and the equivalence Ltac `Equiv` have both been updated to abbreviate the proofs. The code is now only 4,400 lines.

## April 20, 2021
The source code for the verification of *Principia*'s propositional logic proof sketches has been updated. Many proofs have been rewritten with the `Coq` standard library's modules on classical logic and classical logic facts: notably, the axioms of *Principia* have also been proven from these standard libraries. So assuming the `Coq` standard libraries and kernel are kosher, then all the propositional logic proofs are verified on that background system. See the Github repository for the updated code. 

## February 15, 2021
The project has formally verified *Principia*'s propositional logic proof sketches - for all 189 theorems in \*1-to-\*5 - for the very first time. This improves significantly on the earlier computer verification work of Allen Newell *et al*., Hao Wang, and Daniel O'Leary. In all three cases, either some theorems were not verified or their proofs were not reconstructed according to *Principia*'s proof sketches. Our project in contrast reconstructs all the proofs in a way that is faithful to the text: each completion of *Principia*'s proof in `Coq` makes use of every theorem cited in *Principia*'s proof sketch.

# Digital publications
As of February 15, 2021, the *Principia* Rewrite project has also produced:

1. a `LaTeX` package, `principia`, for typesetting any symbol in *Principia*'s Volume I
2. a `Coq` file of *Principia*'s propositional logic (\*1-\*5), running about [4,700 lines of code](https://github.com/LogicalAtomist/principia/blob/master/PL.v) / [113 pages](https://github.com/LogicalAtomist/principia/blob/master/PL.pdf)
3. a pleasingly typeset edition of *Principia*'s first 131 pages in LaTeX, going from its introduction through the end of its propositional logic (up to \*5).

There are further developments to come: a high priority for the project is to build a map of the first five chapters ("starred numbers") of *Principia* - because maps are fun and cool, besides being informative when done well.

# Contact
If you have any questions, criticisms, or thoughts related to the *Principia* Rewrite project, write to `landon dot elkind at wku dot edu`.

![*Principia* & `Coq` side-by-side](PM2.14-2.15.png)
![Sample page of *Principia* digitized with `LaTeX` using the `principia` package](SamplePMalphabeticallistofprops.png)
