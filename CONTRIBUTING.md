# Contributing to SampCert

## Style Guide

SampCert follows the Mathlib4 style guide for [naming conventions](https://leanprover-community.github.io/contribute/style.html), [code style](https://leanprover-community.github.io/contribute/style.html), and [documentation style](https://leanprover-community.github.io/contribute/doc.html). 

Due to extraction, some names intentionally violate the naming scheme. The file ``Extraction.lean`` lists names which must not change. 

### SLang naming scheme

SampCert implements a shallow embedding of a randomized programming language SLang. All SLang programs evaluate to a term of type ``SLang α``, however the opposite is not true since ``SLang α`` values may not have an interpretation as a probability distribution. We distinguish ``SLang α``-producing terms which are well-behaved SLang programs (as in they are normalized and extractable) by prefixing their names with ``prob``, for example ``probGeometric`` or ``probUntil``.

Similarly, SampCert implements a differentially private query language at type ``List α → SLang β``. Terms of this type which are proven differentially private are prefixed ``priv``, such as ``privNoisedBoundedSum`` or ``privNoisedQuery``. 

Barring the exceptions made for extraction, SLang programs should follow this naming scheme. 


## Tools

SampCert uses [doc-gen4](https://github.com/leanprover/doc-gen4) to render its documentation. You can build a local copy using the command ``lake -R -Kenv=doc build SampCert:docs``.

SampCert also installs [import-graph](https://github.com/leanprover-community/import-graph). The command ``lake exe graph --to SampCert import_graph.pdf`` will render a dependency graph between SampCert files. 



