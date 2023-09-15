# Rebuttal

We wish to thank the reviewers for their time and insightful comments. It seems
that the reviewers largely agreed on the strengths (exciting connection between
databases and data planes) and weaknesses (depth, evaluation and presentation)
of the paper. We discuss our plan for addressing the weaknesses in this
response. 

## Overview 

Our vision with this paper is to demonstrate the power of database theory in the
domain of data plane programming, by bringing it to bear on the data plane
emulation problem. Specifically we rely on an algorithm from database theory
called the chase, introducing several extensions of the classical algorithm to
solve our problem. Our contributions are as follows:

- An relational encoding of data plane pipeline programs that let us use the chase
to produce: 
    - a semantics for data planes 
    - a semantics for the data plane emulation problem 
- A novel extension called the priority chase that we use to provide: 
    - a priority-aware semantics for data planes with wildcards
    - an algorithm for computing priorities of target programs in the data plane
      emulation problem
    - A symbolic chase algorithm that gives us the first offline solution to the
      data plane emulation problem 
   - The notion of the generative chase and its generative solutions to provide
     a semantics for the data plane emulation problem with action-data.

__Depth__. Reviewer B objected that there is a mismatch between our motivation
in our introduction and the realities of our technical development. Indeed, upon
revisiting our introduction, we agree that our current introduction sets up the
reader to believe that we are going to develop a mathematical correspondence
between the two fields. Instead, our paper is focused on using database theory
to solve an open problem in networking. We devise special variants of key
database theory concepts (dTGDs and EGDs) and use them to define
networking-specific chase algorithms, computing the first offline algorithm for
control plane mapping. We will adjust our overly poetic introduction to set
expectations appropriately.

With this in mind, we believe our work is sufficiently technically deep to merit
publication. We propose 3 new variants of the chase that rely on nonstandard
formalisms for dependencies, and prove them correct, to solve an open question
in networking.

__Presentation__. We would like to thank the authors for their patience in
reviewing this paper, despite its typos and density. Upon revisiting the text,
we agree that the background sections are too dense to effectively onboard
readers unfamiliar with the out-of-domain concepts: the chase and data planes.
It’s also clear that the later sections of the paper are lacking in
intuition-providing prose. Luckily, with four more pages and nearly three weeks
to revise, we can absolutely add the requested detail. We’ve outlined our
revision plan in the Change List section below.

__Evaluation__. Reviewers A and B both pointed out that an implementation and an
evaluation would strengthen the paper. It seems that the key missing piece is
the scalability, which we’ve stated is exponential in the size of the programs.
Indeed, if we were to do an empirical evaluation of this work, we wouldn’t learn
much beyond what we can compute analytically, since we can directly compute the
size of the search space from the inputs. Our contribution here is intended to
be theoretical: we can effectively model problem solutions in networking using
database theory.

All told, we do believe that our formal contribution, comprising a semantic
model of pipelines, and a solution to the control plane mapping problem via the
formal development of the novel symbolic, priority, and generative chases, are
sufficiently interesting for a POPL audience.

## Change List

We propose the following changes to our work to address the questions of Presentation, Depth, and Evaluation summarized above

__Presentation__
- In section 2, we will provide a clear road map, in a figure, for the technical
contributions of the paper to set expectations and help guide the reader through
the technical space.
- For our background sections (especially 3.2 and 3.3), we will provide examples
and take more time to explain the essential concepts. We expect these sections
to at least double in size. 
- We will weave additional signposting, intuition-providing explanations, and
examples into the later technical sections. 
- We will certainly look for places to simplify our notation. For instance, we
can remove the subscripts on $\phi$ and $\psi$ on line 251, and stick to one
notation for collections of variables wherever possible (e.g. unify $\vec x$ and
$\mathbf{x}$). 
- To provide concreteness to our examples, we will limit our use of the
set-theoretic notation for tables and prefer the concrete match-action
representation as on 106-109. 
- We will fix all copy-editing issues (typos and use-before-def errors)

__Depth__.
- We will make our contribution clearer in the introduction. We are not
  proposing an insightful connection between the two fields but rather a
  wrangling of database theory to solve interesting problems in software defined
  networking. For instance, our verbiage about “building a bridge between
  databases and data planes” could indeed be scaled back to avoid misleading
  readers.

__Evaluation__.
- We will modify the case-study figures (e.g. Fig 3) to include the source and
  target instances notated in the match-action style from the introduction.

## Detailed Response

Here we respond inline to the reviewers' comments.

### Reviewer A

> However, the scalability performance of algorithms in this space is known to
> be a challenge, and although the paper presents some nice small clear
> examples, it is not clear if the approach can overcome these scalability
> issues. Using the chase algorithm is a heavy hammer for the examples provided
> in the paper, but its deployment may be justified with suitability large and
> sophisticated pipelines, however this is yet to be determined. A few more
> practical or experimental analyses and results to help underpin this approach
> would certainly merit a higher score for this paper.

While an implementation is out of the question for this work, we are happy to
include the empirical results describing the size of the search space for our
existing case studies.

#### Detailed Feedback

> Page 4, line 187. "tabls" should be "tables".

Thanks! We’ve made this change.

> Page 5, line 204, I tripped up over the use of "Recall" ~ I don't think the
> half program observation was made earlier in this paper? The "recall" is just
> for readers of this paper that have also read Liu et. al. 2018?

Thanks! We’ll remove this use of “Recall”.

> Page 12, line 580. Perhaps this sentence needs rewriting. "From this point on,
> we will elide the bookkeeping associated explicit with priorities when
> possible."

Thanks! This should be “From this point on, we will elide the bookkeeping
associated with explicit priorities when possible” 

### Reviewer B

> However, the rest of the paper underdelivers. The theoretical connection
> established between networking and databases seems to be a simple encoding
> that treats everything as relations. Deeper, insightful connections and
> results would make the paper much stronger.

While the paper does start with a simple relational encoding of match-action
tables into relations, this simplicity should not be seen as a downside. In
fact, other relational encodings of data planes either make significant
simplifying assumptions, or only exploit superficial similarities between
match-action tables and database tables. Our work models the core
match-action abstraction, and we are able to show that this approach is valuable
by using it to solve an open problem in networking.

From this point on in the paper, we endeavor to show that thinking of match
action-table pipelines relationally is very powerful. The majority of the paper
is focused on solving the control plane mapping problem, which requires
introducing new variants of the chase (priority, symbolic, generative). Indeed
this is the meat of our contribution.

> Further, my major concern is actually about the presentation which also leads
> to my overall recommendation. If I just peek through the paper, I get the
> rough idea of each section or subsection, but once I zoom in to the technical
> details and formalism, I get lost quite quickly. Overall the text and the
> formulae are interleaved but not really connected. In too many cases,
> terminologies and notations pop out abruptly in the text without prior
> explanation and definition, quite a few mathematical notations are excessive
> unnecessary, and formulae are put in places not very related to the context.
> Examples are needed in many places.

We agree. We can insert signposts and examples where necessary. We will also
work to reduce the notational burden on the reader.

> And the number of typos exceeds the negligible level.

The paper is quite inundated with typos. We apologize deeply for these
oversights. Luckily, these can be fixed in shepherding.

> Some examples are given at the end of the review.

Thanks! We’ve addressed these below.

> Besides the presentation defects, the paper also lacks a solid evaluation
> component. The vast majority of the paper is dedicated to the process of
> encoding toward a formulation that can be handled by the chase algorithm, and
> it is not clear at all what happens beyond that.

As we described above, we are happy to provide the search space size for our
case studies, however we believe that the theoretical contributions suffice for
publication.

> How is the problem solved? Is the problem just sent to an off-the-shelf
> implementation of the chase framework?

Because of our technical changes to the chase, we cannot simply send it off to a
solver.

> Did the paper actually solve the case study?

Yes! The solutions to the case studies are presented in the examples themselves.
We will be sure to highlight this by using the table notation to depict the
solved tables.

> How's the result/performance compared to existing approaches, e.g., Avenir as
> mentioned in the paper?

This is unknown. But we can provide an analytical justification for this paper’s
superiority. Avenir’s runtime is bounded by the number of possible rule
combinations that can be inserted into the target table—its performance relies
heavily on an ad-hoc collection of heuristics. The performance of the chase
algorithms in this paper are bounded by the size of the source instance and the
number of paths in the target program, which is much smaller.

#### Specific Questions 

> Besides the encoding presented in the paper, is there any fundamental
> connection between data plane programming and database theory that can be
> leveraged to benefit both areas?

This paper shows one example of how the simple relational encoding can benefit
the networking domain, by solving the open control plane emulation problem. We
believe that there are _many_ database technologies that we can use to benefit
networking, for example data provenance or query optimization. 

The other direction is less clear. We expect that efficient compression and
matching algorithms such as those used in networking hardware (e.g. LPM and
TCAM) could allow more efficient data representation in certain application
domains.

#### Detailed Feedback

> line 33: ...we use the [the] chase…

Thanks! This has been fixed.

> line 99: ...where RR is [is] the…

Thanks! This has been fixed.

> line 157: it is not clear what the "cross product" exactly means.

This is a good point. Here we use the term loosely. We intended it to be
evocative, but not technical, since the combine table on lines 160- 167 is not
technically the cross product of the tables.

We construct it thusly. For each match-action row (m0,a0) in the first table,
and each match-action row (m1, a1) in the second table we produce a row that
loosely corresponds to (m0, m1, a0, a1). We then simplify the table following
the idempotence of allow and deny and the fact that any deny will supersede an
allow to simplify the set of actions and rows. These are intuitions from the
reality of network programming that we do not include in our description.

We will remove the use of “cross product” and replace it with more precise and
descriptive prose.

> lines 221-224: the formulae are out of nowhere -- why are they here?

Lines 213 - 220 introduces the concept of semantics of pipelines and then lines
221-224 define them. We will be sure to signpost this by adding the line “We
define the semantics of pipelines in the equations below.” There is also a typo
on line 213 that uses banana brackets instead of Strachey brackets for the
semantics. We will fix this as well.

> line 235: the difference between tuple-generating and equality-generating is
> not clear. More explanation and justification needed to show why these kinds
> of dependencies are permitted.

Briefly, an EGD is a dependency whose head is an equality between variables. A
TGD is a dependency whose head is a logical formula over relations only. Indeed
there is a typo here on line 240. EGDs should be $\forall \mathbf{x}.
\phi(\mathbf{x}) \to x_0 = x_1$, where $x_0, x_1 \in \mathbf{x}$. They are
permitted simply because the chase algorithm is defined explicitly in terms of
these rules. We are happy to provide intuition for why these forms are easy to
define chase algorithms for. Following collective feedback that section 3 is too
dense, we will be sure to pepper in examples and more explanatory prose and
context throughout.

> line 305: $a−j$ => $a_j$

Thanks! This has been fixed.

> line 312: I am confused with A(x,x′) and aj(x)=x′ -- why A becomes aj​? What's
> the difference between A and a?

Following the definitions, an $a_j$ is a syntactic representation of the
actions. $A_j$ is the relational interpretation of the action itself. We use
$a_j(\mathbf{x})=\mathbf{x’}$ as syntactic sugar for $A_j(\mathbf{x},
\mathbf{x’})$ for notational simplicity and familiarity, despite the fact that
it is not syntactically well-defined: $a_j$ is syntax, has no binding construct,
and must be interpreted to be run. In hindsight, this is confusing. We propose
to stick to the $A_j$ notation in the final version.

> lines 340-342: the one-point rules are confusing and I got lost. Explain more.

Thanks! Loosely, the one-point rule says that if we have $x=y => \phi(x)$ we can
rewrite this as $\phi(y)$. It lets us perform the substitutions indicated by the
actions in the body of the dependency on the head. This is why the rules have no
explicit actions, because they’ve been substituted away.

Our purpose here was to simplify the complexity of the formulas. We’ll either
draw this out more carefully or include the literal actions depending on which
is more clear.

> line 418: what is "chase over dependencies"? Not defined anywhere and no idea
> what it is.

Good catch. We don’t define this specifically. In definition 3.2 we define “A
chase tree of $\rho$ over $\Sigma$” where $\Sigma$ is a set of dependencies. It
is common in the chase literature to use the verb “chase” to mean “run the chase
algorithm” or “compute the chase tree”. We combined these without providing such
an explanation. We’ll explain this jargon clearly in section 3.2 and remove
earlier references to it (e.g. on line 172).

> line 497: "chase tree" needs definition and explanation.

“Chase tree” is defined in Definition 3.2 on line 287. We will add more
explanation and a visual example after the definition so it is not so easy to
miss.

> lines 524-527: why the formula is shown here?

These denotational priority semantics for pipelines, as motivated in the
previous paragraph. We will add prose to explicitly signpost the relationship.

>  The ⊴R is not defined.

Thanks for spotting the use-before-def! It is meant to indicate the priority
relationship attached to the relation R. We’ll be sure to fix this during the
revision period.

> line 628: "Recall that Avenir..." You did not mention Avenir anywhere before…

Thanks! We’ve removed “Recall”

> line 662: "Now well" => "Now we'll" ?

Thanks! We’ve made this change.

> line 812: ...were ma[n]y ways...

Thanks! We’ve made this change.

### Reviewer C

> Unfortunately, I found the paper quite hard to follow. It assumes a lot of
> background knowledge on diverse topics such as the chase and network
> data planes, and I don't think that the background section of the paper does
> enough to get a reader on board. I found sections 3.2 and 3.3 quite confusing
> despite already being familiar with the chase.

We apologize for the confusing nature of our exposition. We will include more
detail and explanatory examples in these early sections.

> Many definitions there and elsewhere in the paper are incomplete, confusing,
> seemingly erroneous, or lacking intuition-providing explanations (see detailed
> comments).

We agree that the definitions are confusing and lacking intuition-providing
explanations. As discussed above, we will fix this in the camera ready. 

There are also a few that had unfortunate typos which we have already fixed,
however the underlying definitions are themselves correct. We could not find any
that were incomplete. We will make sure to add explanatory prose to clarify the
slightly counter-intuitive nature of the definitions.

#### Detailed Feedback

> 61: "solved the data plane emulation" [problem]

Thanks! We’ve made this change.

> 123: "first-order formulas": this gives the impression that the chase can
> solve any first-order theory, but the chase may not terminate. Also, the chase
> constructs a universal instance; Otherwise, an instance that "has everything
> in it" trivially satisfies any TGDs and EGDs.

Good point. The chase does make certain structural requirements on the set of
first-order formulas. We hope to elide universality in our presentation here as
it is actually not the right notion for us. See the discussion on generative
solutions, though it seems worth mentioning for readers familiar with the chase.

> 172: what does "refines" mean here?

As defined on line 380, a pipeline-instance pair $s[\varsigma]$ refines another
pipeline-instance pair $t[\tau]$ if the semantics of $s[\varsigma]$, when
interpreted as a relation, are a subset of the semantics of $t[\tau]$ when
interpreted as a relation. Informally $s[\varsigma]$ may be defined on fewer
packets, but whenever $s[\varsigma]$ is defined on a packet, then $t[\tau]$ is
defined on that packet _and_ produces an equivalent output packet.

Upon review this early occurrence of "refines" seems out of place and
unnecessary. We'll revise the text to eliminate it.

> 187: "tabls"
> 208: use of bold for vector instead of overline
> 210: "is the case is" 

Thanks! We’ve made these changes

> 3.1 could use some examples 

We’ll be sure to include some!

> 221: A seems undefined?

The function $\mathcal{A}\llbracket-\rrbracket : \mathsf{Action} -> \mathsf{Pkt} -> \mathsf{Pkt}$ is
defined on lines 222 - 224.

> 237: Are phi and psi arbitrary first order sentences? It seems later they have
> to be in certain forms (disjunctive normal forms for head for example).

Thanks! We’ll add this detail.

> 242: what is x=beta(x)? should it be just beta(x)? It might be simpler to just
> say u=v for u, v in x then use beta.

Precisely. This is a typo. Beta is used in FDGs only.

> 242: what are the differences between FGDs and TGDs? Is it that TGDs don't
> allow equalities?

The head of TGDs can only be conjunctions of relation symbols (i.e. no
equalities). However FDGs are more expressive than just equalities. The heads of
FDGs are quantifier-free sentences over some decidable interpreted theory that
we leave abstract. In our case, it suffices to think of them as sentences in the
theory of quantifier-free fixed-width bit vectors (QFBV).

> 248: Consider citing some of the literature on dTGDs and disjunctive Datalog,
> e.g. https://dl.acm.org/doi/pdf/10.1145/2976736

Thanks! We’ll include this, and others.

> 261: Σs​ and Σt undefined

Thanks! These lines should be moved to section 5.2.

> 268: angle brackets undefined

Thanks! These are taken from [Fagin et al. 2005b] to indicate union over
disjoint schemas. We'll be sure to define them explicitly.

> 269: data exchange deserves at least a brief explanation

Yep! As with the previous two comments, this was a result of some last minute
reorganization. This needs to be moved to section 5.2

> 271: the dTGD form here does not have existential quantifiers. Handling of
> existential quantifiers is usually the most delicate part of a chase
> algorithm.

Good point. The standard treatment of existential quantifiers is insufficient
and indeed incorrect for our setting. We intentionally omit existential
quantifiers until section 9 where we discuss our more restrictive notion of
generative solutions. We’ll make sure to explicitly acknowledge this quirk of
our presentation.

> 280: what about the success case for FGDs?

As with EDGs in the standard chase [Fagin et al. 2005b], there is no success
case. Or rather, since we cannot say that “$d$ can be applied to $\rho$ with
homomorphism $h$”, if $\beta(x)$ succeeds we say “$d$ can_not_ be applied to
$\rho$ with homomorphism $h$”. This simply means that the rule does not apply.
We’ll be sure to draw attention to this subtlety.

> 298: what does x = Var mean?

That’s a typo, should be $\subseteq$, not $\eq$. It’s been fixed.

> 305: R1 or R0​? Seems zero-indexed from line 298

Yes! $R_0$. The formula on line 305 has it correctly as well. It’s been fixed.

> 305: Instead of a−j do you mean aj​?

Thanks! We’ve fixed this.

> 324: What is κ′?

Thanks! That should just be κ. We’ve fixed this.

> 376: what's the intuition of refinement? if a⊑a′, does this mean a' always
> produces more packets than a?

In fact, this line should have been deleted, as a⊑a′ is not used anywhere else.
Actions are total, deterministic functions, so here refinement is actually just
equality.

> 440: How is this different from a normal EGD 
> ∀...,R(k,i0),R(k,i1)=>i0=i1?

The point here is a bit subtle. These two are semantically equivalent, but the
bodies induce different homomorphisms. Homomorphisms are triggered based on the
body of the rule, not the head, so putting the fact that the keys must be equal
in both tables in the body of the rule increases the valid homomorphisms.

We defined it this way once-and-for-all to avoid having to tweak the definition
again in 6.1.

> 6.1: How do priority homomorphisms work for rule bodies with multiple atoms?
> Some examples will be helpful.

It uses a lexicographic order. We’ll include this subtlety, and augment the
example on line 551 to incorporate it.

> 547: is variable i overloaded/shadowed here?

Yep! This is a typo. The subscript should be $j = 1$. We’ve made this change.

> 850: Bu​ should be Bi​

Thanks! We’ve made this change.

> 9.2: Now there are existentials, so termination is no longer obvious. Does
> your algorithm terminate?

Absolutely. As before, we have no cycles of any kind in our dependencies. We’ll
be sure to state this explicitly.

> 1150: I find it easier to understand the problem by thinking of data plane
> emulation as a program synthesis problem, since this gives the intuition of
> why we should use disjunctive dependencies. This connection is made here in
> the related work section but it might be beneficial to mention this early on.

Thanks! We’ll add this analogy to an early section.

