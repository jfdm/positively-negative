# Adventures in being Positively Negative

> A linguistics professor was lecturing their class the other
> day. "In English," they said, "a double negative forms a
> positive. However, in some languages, such as Russian, a double
> negative remains a negative. But there isn't a single language, not
> one, in which a double positive can express a negative."
>
> A voice from the back of the room piped up, "Yeah, right."

Adapted from https://www.ling.upenn.edu/~beatrice/humor/double-positive.html

Dependently-typed programmers are keen to espouse the idea that:
**Propositions are Types; Proofs are Programs**.
Due to the *Curry-Howard* correspondence, a common design idiom in languages such as Agda & Idris is to use *predicates* and their *decision procedures* to represent truths (predicates) and a way to discern if the truth is evident (the decision procedure).
Predicates are positive pieces of information, and using their decision procedures forces us to tread the happy (positive) path at runtime.
Treading this 'happy path', however, curtails all traces of *negative* information (falsity) to a careless compile time whisper.
To enable reporting of negative information we must rethink what it means to be negative and by smearing our negativity with a veneer of positivity we can start to report negative information more positively.

This package is an experiment investigating what it means to be a `decidable predicate` and how that affects the design of our programs in Idris.

The goal is that, by being positively negative, we get richer information about why our programs fail and not *just* that they did.

This experiment is heavily inspired by Bob Atkey's MSFP 2022 talk *Data Types with Negation* [^1][^2] held at MSFP '22 [^3] in which he reported on the idea of using *Constructive Negation* to be more positively negative.
Specifically, when I shouted into the abyss about writing better error reporting instances of `Dec` the abyss (Bob) shouted back with the core observation required to get things going.

[^1]: https://www.youtube.com/watch?v=mZZjOKWCF4A
[^2]: https://msfp-workshop.github.io/msfp2022/atkey-abstract.pdf
[^3]: https://msfp-workshop.github.io/msfp2022/
