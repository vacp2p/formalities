---- MODULE MC ----
EXTENDS MVDS, TLC

\* CONSTRAINT definition @modelParameterContraint:0
constr_15730079799954000 ==
\/ \A n \in Node : \A s \in Node \ {n} : state[n][s] # "delivered"
----
=============================================================================
\* Modification History
\* Created Wed Nov 06 03:39:39 CET 2019 by deaneigenmann
