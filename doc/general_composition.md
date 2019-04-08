---
header-includes:
  - \usepackage{bussproofs}
  - \usepackage{unixode}
---

# General Composition

## Tuple Functors

Write $n \colon \mathbb N$ to mean $n$ has type $\mathbb N$. (For the reader unfamiliar with type theory, it's safe to interpret this to mean $n\in \mathbb N$.)  For $n \colon \mathbb N$, we denote and define $\underline{n} = \{0, 1, \dots, n-1\}$.

For $m \colon \mathbb N$, denote and define the $\mathrm{mtuple}$ functor on Set as follows: 

+ \underline{on objects}: if $A$ is a Set, then $\mathrm{mtuple} A = \{(a_{0}, \dots, a_{m-1}) \mid a_{i} \colon A\}$

+ \underline{on arrows}: if $f \colon A \to B$ is a function from the set $A$ to the set $B$, then $\mathrm{mtuple} f \colon \mathrm{mtuple}A \to \mathrm{mtuple}B$ is defined for each $(a_{0}, \dots, a_{m-1})$ of type $\mathrm{mtuple}A$ as follows: $$\mathrm{mtuple}f (a_0, \dots, a_{m-1}) = (f a_0, \dots, f a_{m-1}),$$ which inhabits the type $\mathrm{mtuple} A$.

Notice that $\mathbf a$ has type $\mathrm{mtuple} A$ iff we can represent $\mathbf a$ as a function of type $\underline{m} \to A$; that is, iff we can represent the mtuple $(a_0, \dots, a_{m-1})$ as a function, $\mathbf a$, where $\mathbf a(i) = a_i$ for each $0\leq i < n$.  Thus, we have the following equivalence of types: $\mathrm{mtuple} A \cong \underline{m} \to A$.

Let $\mathbf m = (m_0, \dots, m_{n-1}) \colon  \mathrm{ntuple} \mathbb N$.  Define the $\mathbf{mtuple}$ functor as follows: 

+ \underline{on objects}: if $A$ is a Set, then $$\mathbf{mtuple} A = \{((a_{00}, \dots, a_{0(m_1-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(m_n-1)})) \mid a_{ij} \colon A\}$$ (We may write $\mathbf a_i$ in place of $(a_{i0}, \dots, a_{i(k-1)})$, if $k$ is clear from context.)

+ \underline{on arrows}: if $f$ is a function from the set $A$ to the set $B$, then $\mathbf{mtuple} f \colon \mathbf{mtuple}A \to \mathbf{mtuple}B$ is defined for each $(\mathbf a_1, \dots, \mathbf a_n)$ in $\mathbf{mtuple}A$ as follows: \begin{align*}\mathbf{mtuple} f (\mathbf a_1, \dots, \mathbf a_n) &= (\mathrm{m_1tuple}f \mathbf a_1, \dots, \mathrm{m_ntuple}f \mathbf a_n)\\ &= ((f a_{11}, \dots, f a_{1m_1}), \dots, (f a_{n1}, \dots, f a_{nm_n})).\end{align*}

Notice that $\mathbf a_i$ has type $\mathrm{m_ituple} A$ iff it can be represented as a function of type $\underline{m_i} \to A$; that is, iff the tuple $(a_{i0}, \dots, a_{i(m_i-1)})$ is (the graph of) the function defined by $\mathbf a_i(j) = a_{ij}$ for each $0\leq j < m_i$.  Thus, if $\mathbf m = (m_0, \dots, m_{n-1}) \colon \mathrm{ntuple} \mathbb N$, then $\mathbf{mtuple} A$ is the *dependent function type*, $$\prod_{i \colon \underline{n}} (\underline{m_i} \to A).$$



\newcommand\fork{\mathrm{fork}}
\newcommand\eval{\mathbf{eval}}
<!-- \newcommand\deval{\mathbf{eval}} -->
\newcommand\dfork{\mathbf{fork}}

### Fork and Eval

Define $\fork : (A \to B)\to (A \to C) \to A \to (B \times C)$ as follows: if $f \colon A \to B$, $g \colon A \to C$, and $a \colon A$, then $\fork (f) (g) (a) = (f (a), g (a))$. (A more standard definition of fork might take the domain to be $(A \to B)\times (A \to C)$, whereas we have described a "curried" version in order to support partial application.)

The fork function generalizes easily to dependent function types.  Let $A$ be a type and for each $a \colon A$ let $B_a$ and $C_a$ be types. Define the *dependent fork*, denoted by $$\dfork : \prod_{a : A} B_a\to \prod_{a : A} C_a \to \prod_{a : A}(B_a \times C_a),$$ as follows: if $f \colon \Pi_{a : A} B_a$, $g \colon \Pi_{a : A} C_a$, and $a \colon A$, then $\dfork (f) (g) (a) = (f (a), g (a))\colon B_a \times C_a$. Since we use a curried definition, we can partially apply $\dfork$ and obtain the expected typing relations, viz., $$\dfork (f) \colon \prod_{a:A} C_a \to \prod_{a:A} (B_a \times C_a)\quad \text{ and } \quad \dfork (f) (g) \colon \prod_{a:A} (B_a \times C_a).$$

Next, let $\eval \colon (A \to B) \times A$ denote function application; that is, $\eval (f, a) = f a$, if $f \colon A \to B$ and $a \colon A$. Thus, if $h \colon \prod_{a : A}(C_a \to D)$, $k \colon \prod_{a : A}C_a$, and $a\colon A$, then $$\dfork (h)(k)(a) = (h(a), k(a)) \colon (C_a \to D) \times C_a, \text{ and }$$ $$\eval\, \dfork (h)(k)(a) = h(a)k(a) \colon D.$$
<!-- Now, let $D$ be a type and let $A$ and $C_a$ be as above. Define the **dependent eval**, denoted by $\deval \colon \prod_{a : A}(C_a \to D) \times \prod_{a : A} C_a$ as follows:  -->

### General Composition of Operations on a Set

In universal algebra we deal mainly with *finitary operations on sets*. By an *$n$-ary operation* on the set $A$ we mean a function $f \colon A^n \to A$, that takes $n$ inhabitants of the type $A$ and returns an element of type $A$.\footnote{Using the tuple constructor described in the last section, we could also represent such an operation as $f \colon \mathrm{ntuple} A \to A$, but we prefer to reserve ntuple for instances in which it acts as a functor.} By the equivalence of the $\mathrm{ntuple}$ type and the function type $\underline{n} \to A$, we may represent the type of $n$-ary operations on $A$ by $(\underline{n} \to A) \to A$.  Evaluating such an $f \colon (\underline{n} \to A) \to A$ at a tuple $a \colon \underline{n} \to A$ is simply function application, expressed by the usual rule (sometimes called "implication elimination" or "modus ponens"):
<!-- $f \mathbf a = f(\mathbf a(0), \dots, \mathbf a(n-1)) \colon A$. -->

\begin{prooftree}
\AxiomC{$f \colon (\underline{n} \to A) \to A$}
\AxiomC{$a \colon \underline{n} \to A$}
\RightLabel{$_{(\to \mathrm{E})}$}
\BinaryInfC{$f a \colon A$}
\end{prooftree}
If we let $a_i$ denote the value of $a$ at $i$, and if we identify $a$ with it's graph (the tuple $(a_0, \dots, a_{n-1})$), then $f a = f(a_0, \dots, a_{n-1})$.

Denote and define the collection of all finitary operations on $A$ by $$\operatorname{Op}A = \bigcup_{n<\omega} (A^n \to A)\cong \bigcup_{n<\omega} ((\underline{n} \to A) \to A).$$

We will now try to develop a formulation of *general function composition* that is more elegant and computationally practical than the standard formulation.  Let us first briefly review the standard formulation of function composition.  Let $f \colon (\underline{n} \to A) \to A$ be an $n$-ary operation on $A$, and suppose for each $0\leq i < n$ we have an operation $g_i \colon (\underline{k_i} \to A) \to A$.  Then we define $f \circ (g_0, \dots, g_{n-1})$ in the following standard way: for each $$((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\colon A^{k_0} \times \cdots \times A^{k_{n-1}},$$ \vskip-5mm \begin{align*}(f\circ &(g_0, \dots, g_{n-1}))((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\ &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).\end{align*}

Not only is this notation tedious, but also it lends itself poorly to computation. To improve upon it, let us first consider the ntuple $(g_0, \dots, g_{n-1})$. This is an ntuple of operations from $\operatorname{Op}A$. If we denote by $g$ the function from $\underline{n}$ to $\operatorname{Op}A$ given by $g i = g_i$ for each $0\leq i < n$, then $g$ inhabits the following dependent function type: $$\prod_{i : \underline{n}}  ((\underline{k_i} \to A) \to A).$$

Next, define the function $a$ as follows: $a i \colon \underline{k_i} \to A$ for each $0\leq i < n$ and for each $j\colon \underline{k_i}$, $a i j = a_{ij}$. Then the ntuple of arguments in the expression above can be identified with the tuple $a = (a 0, \dots, a (n-1))$ of functions. Thus $a$ has dependent function type $\prod_{i : \underline{n}} (\underline{k_i} \to A)$, and for each $i\colon \underline{n}$, we have $a i j = a_{ij}$.

Now, looking back at the section above, where we defined the fork and eval functions, we can see how to perform general composition using dependent types.  If $g \colon \Pi_{i : \underline{n}}  ((\underline{k_i} \to A) \to A)$, and $a \colon \Pi_{i : \underline{n}}(\underline{k_i} \to A)$, then $$\dfork (g) (a) (i) = (g(i), a(i)) \colon ((\underline{k_i}\to A) \to A) \times (\underline{k_i}\to A)$$ and $\eval (\dfork (g) (a) (i)) = g(i) a(i) \colon A$.
Observe that the codomain $A$ does not depend on $i$, so the types $\Pi_{i:\underline{n}} A$ and $\underline{n} \to A$ are equivalent. Therefore, $\eval \circ \dfork (g) (a) \colon \underline{n} \to A$.  On the other hand, we have $$\eval\circ \dfork (g) \colon \prod_{i : \underline{n}}  (\underline{k_i} \to A) \to (\underline{n} \to A).$$  Thus, if we take an $n$-ary operation, $f\colon (\underline{n} \to A) \to A$, and an $n$-tuple of operations, $g\colon \Pi_{i : \underline{n}} ((\underline{k_i} \to A) \to A)$, then we can compose $f$ with $g$ as follows: $$f [g] := f (\eval\circ \dfork(g)) \colon \prod_{i : \underline{n}}(\underline{k_i} \to A) \to A.$$  Indeed, if $a \colon \Pi_{i : \underline{n}}(\underline{k_i} \to A)$, then  $\eval\circ \dfork(g)(a)$ has type $\underline{n} \to A$, which is the domain type of $f$; therefore, $f (\eval\circ \dfork(g) (a))$ has type $A$, as desired.


<!-- 
$$\eval\, \dfork (g) (a) \colon \underline{n} \to A \quad \text{ and } \quad \eval\, \dfork (g) \colon \prod_{i : \underline{n}}  (\underline{k_i} \to A) \to (\underline{n} \to A).$$ Thus, if $f\colon \underline{n} \to A$ is an $n$-ary operation on $A$, and $g\colon \Pi_{i : \underline{n}}  ((\underline{k_i} \to A) \to A)$ is an "$n$-tuple" of operations on $A$, then we can define the general composition of $f$ with $g$ as follows: $$f [g] := f \, \eval\, \dfork (g).$$ -->

<!-- Now let $$(g \otimes a) i = g_i (a i) = g_i (a_{i0}, \dots, a_{i(k_i-1)}).$$ Then $g \otimes a \colon \underline{n} \to A$.  Therefore, if $f \colon \underline{n} \to A$, we can compose as follows: \begin{align*}(f \circ g) (a) &= f ( g \otimes a ) \\ &= f( (g\otimes a)0, \dots, (g \otimes a)(n-1))\\ &=f( g_0(a 0), \dots, g_{n-1}(a (n-1))). \end{align*}
Let $\mathbf{k} = (k_1, \dots, k_n)$ be the tuple of arities of the $g_i$'s.  Then $$((a_{11}, \dots, a_{1k_1}), \dots, (a_{n1}, \dots, a_{nk_n})) \colon \mathbf{ktuple} A.$$  Now $(g_1, \dots, g_n)$ is a tuple of a certain type.  What is that type?  For each $1\leq i \leq n$, we have $g_i \colon \mathrm{k_ituple} A \to A$ ...so...?
Notice that $\mathbf k$ has type $\mathrm{ntuple} \mathbb N = \{(k_1, \dots, k_n) \mid k_i \colon \mathbb N\}$.
$$\mathrm{ntuple}(\operatorname{Op}A) \cong \underline{n} \to \operatorname{Op}A.$$
\begin{prooftree}
\AxiomC{$g \colon \underline{n} \to \operatorname{Op}A$}
\AxiomC{$a \colon \prod_{(i : \underline{n})} (\underline{\rho g_i} \to A)$}
\BinaryInfC{$(g i) (a i) \colon A$}
\end{prooftree}
$$\mathrm{ntuple}(\operatorname{Op}A) \cong \prod_{(i : \underline{n})} \prod_{(g_i : \mathrm{Op} A)} ((\underline{\rho g_i} \to A) \to A).$$
$$\mathrm{ntuple}(\operatorname{Op}A) \cong \underline{n} \to \prod_{g \colon \operatorname{Op}A} ((\rho g \to A) \to A).$$
$$\prod_{g : \underline{n} \to \operatorname{Op}A} (\underline{\rho g} \to A).$$
Can we *define* $\mathbf{ktuple}$ on $\operatorname{Op}A$ as follows?
$$\mathbf{ktuple}(\operatorname{Op}A) = \{(g_1, \dots, g_n) \mid g_i \colon A^{k_i} \to A\}$$
Let $\rho \colon \operatorname{Op}A \to \mathbb N$ be the *arity function*; that is, if $g \colon (\underline{k} \to A) \to A$ is a *$k$-ary* operation on $A$, then $\rho g = k$. -->


<!-- ## Product Bifunctor.  Product $\times$ forms a bifunctor; in Set, for types $A$ and $B$, the type $A\times B$ consists of pairs $(a,b)$, where $a : A$ and $b: B$. -->

<!-- , and $g$ obeys the following function application rule:
\begin{prooftree}
\AxiomC{$g \colon (\underline{k} \to A) \to A$}
\AxiomC{$a \colon \underline{k} \to A$}
\RightLabel{$_{(\to \mathrm{E})}$}
\BinaryInfC{$g a \colon A$}
\end{prooftree} -->
