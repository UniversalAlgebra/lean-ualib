Composition
===========

Tuple Functors
--------------

For :math:`m \colon \mathbb N`, denote and define the :math:`\mathrm{mtuple}` functor on Set as follows:

:on objects: if :math:`A` is a Set, then :math:`\mathrm{mtuple} A = \{(a_{0}, \dots, a_{m-1}) \mid a_{i} \colon A\}`

:on arrows: if :math:`f \colon A \to B` is a function from the set :math:`A` to the set :math:`B`, then :math:`\mathrm{mtuple} f \colon \mathrm{mtuple}A \to \mathrm{mtuple}B` is defined for each :math:`(a_{0}, \dots, a_{m-1})` of type :math:`\mathrm{mtuple}A` as follows:

.. math:: \mathrm{mtuple}f (a_0, \dots, a_{m-1}) = (f a_0, \dots, f a_{m-1}),

which inhabits the type :math:`\mathrm{mtuple} A`.

Notice that :math:`\mathbf a` has type :math:`\mathrm{mtuple} A` iff we can represent :math:`\mathbf a` as a function of type :math:`\underline{m} \to A`; that is, iff we can represent the mtuple :math:`(a_0, \dots, a_{m-1})` as a function, :math:`\mathbf a`, where :math:`\mathbf a(i) = a_i` for each :math:`0\leq i < n`. Thus, we have the following equivalence of types: :math:`\mathrm{mtuple} A \cong \underline{m} \to A`.

Let :math:`\mathbf m = (m_0, \dots, m_{n-1}) \colon \mathrm{ntuple} \mathbb N`. Define the :math:`\mathbf{mtuple}` functor as follows:

:on objects: if :math:`A` is a Set, then

.. math:: \mathbf{mtuple} A = \{((a_{00}, \dots, a_{0(m_1-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(m_n-1)})) \mid a_{ij} \colon A\}

(We may write :math:`\mathbf a_i` in place of :math:`(a_{i0}, \dots, a_{i(k-1)})`, if :math:`k` is clear from context.)

:on arrows: if :math:`f` is a function from the set :math:`A` to the set :math:`B`, then :math:`\mathbf{mtuple} f \colon \mathbf{mtuple}A \to \mathbf{mtuple}B` is defined for each :math:`(\mathbf a_1, \dots, \mathbf a_n)` in :math:`\mathbf{mtuple}A` as follows:

.. math::

    \mathbf{mtuple} f (\mathbf a_1, \dots, \mathbf a_n) &= (\mathrm{m_1tuple}f \mathbf a_1, \dots, \mathrm{m_ntuple}f \mathbf a_n)\\
                              &= ((f a_{11}, \dots, f a_{1m_1}), \dots, (f a_{n1}, \dots, f a_{nm_n})).

Notice that :math:`\mathbf a_i` has type :math:`\mathrm{m_ituple} A` iff it can be represented as a function of type :math:`\underline{m_i} \to A`; that is, iff the tuple :math:`(a_{i0}, \dots, a_{i(m_i-1)})` is (the graph of) the function defined by :math:`\mathbf a_i(j) = a_{ij}` for each :math:`0\leq j < m_i`.

Thus, if :math:`\mathbf m = (m_0, \dots, m_{n-1}) \colon \mathrm{ntuple} \mathbb N`, then :math:`\mathbf{mtuple} A` is the *dependent function type*,

------------------------------------------------

.. math:: \prod_{i \colon \underline{n}} (\underline{m_i} \to A).

Fork and Eval
-------------

Define :math:`\mathrm{fork} : (A \to B)\to (A \to C) \to A \to (B \times C)` as follows: if :math:`f \colon A \to B`, :math:`g \colon A \to C`, and
:math:`a \colon A`, then :math:`\mathrm{fork} (f) (g) (a) = (f (a), g (a))`.

(A more standard definition of fork might take the domain to be :math:`(A \to B)\times (A \to C)`, whereas we have described a "curried" version in order to support partial application.)

The fork function generalizes easily to dependent function types. Let :math:`A` be a type and for each :math:`a \colon A` let :math:`B_a` and
:math:`C_a` be types. Define the *dependent fork*, denoted by

.. math:: \mathbf{fork} : \prod_{a : A} B_a\to \prod_{a : A} C_a \to \prod_{a : A}(B_a \times C_a),

as follows: if :math:`f \colon \Pi_{a : A} B_a`, :math:`g \colon \Pi_{a : A} C_a`, and :math:`a \colon A`, then :math:`\mathbf{fork} (f) (g) (a) = (f (a), g (a))\colon B_a \times C_a`. Since we use a curried definition, we can partially apply :math:`\mathbf{fork}` and obtain the expected typing relations, viz.,

.. math:: \mathbf{fork} (f) \colon \prod_{a:A} C_a \to \prod_{a:A} (B_a \times C_a)\quad \text{ and } \quad \mathbf{fork} (f) (g) \colon \prod_{a:A} (B_a \times C_a).

Next, let :math:`\mathbf{eval} \colon (A \to B) \times A` denote function application; that is, :math:`\mathbf{eval} (f, a) = f a`, if :math:`f \colon A \to B` and :math:`a \colon A`. Thus, if :math:`h \colon \prod_{a : A}(C_a \to D)`, :math:`k \colon \prod_{a : A}C_a`, and :math:`a\colon A`, then

.. math:: \mathbf{fork} (h)(k)(a) = (h(a), k(a)) \colon (C_a \to D) \times C_a, \text{ and }

.. math:: \mathbf{eval} \circ \mathbf{fork} (h)(k)(a) = h(a)k(a) \colon D.

-----------------------------------------------

Example: **Set**
----------------

In universal algebra we deal mainly with *finitary operations on sets*.

By an :math:`n`-**ary operation** on the set :math:`A` we mean a function :math:`f \colon A^n \to A`, that takes :math:`n` inhabitants of the type :math:`A` and returns an element of type :math:`A`. [1]_

By the equivalence of the :math:`\mathrm{ntuple}` type and the function type :math:`\underline{n} \to A`, we may represent the type of :math:`n`-ary operations on :math:`A` by :math:`(\underline{n} \to A) \to A`.

Evaluating such an :math:`f \colon (\underline{n} \to A) \to A` at a tuple :math:`a \colon \underline{n} \to A` is simply function application,
expressed by the usual rule (sometimes called "implication elimination" or "modus ponens").

.. raw:: latex

   \begin{prooftree}
   \AxiomC{$f \colon (\underline{n} \to A) \to A$}
   \AxiomC{$a \colon \underline{n} \to A$}
   \RightLabel{$_{(\to \mathrm{E})}$}
   \BinaryInfC{$f a \colon A$}
   \end{prooftree}

If we let :math:`a_i` denote the value of :math:`a` at :math:`i`, and if we identify :math:`a` with it's graph (the tuple :math:`(a_0, \dots, a_{n-1})`), then
:math:`f a = f(a_0, \dots, a_{n-1})`.

Denote and define the collection of all finitary operations on :math:`A` by

.. math:: \mathrm{Op}(A) = \bigcup_{n<\omega} (A^n \to A)\cong \bigcup_{n<\omega} ((\underline{n} \to A) \to A).

We will now try to develop a formulation of *general function composition* that is more elegant and computationally practical than the standard formulation, but first, let us first briefly review the standard formulation of function composition.

Let :math:`f \colon (\underline{n} \to A) \to A` be an :math:`n`-ary operation on :math:`A`, and suppose for each :math:`0\leq i < n` we have an operation :math:`g_i \colon (\underline{k_i} \to A) \to A`. Then we define :math:`f \circ (g_0, \dots, g_{n-1})` in the following standard way: for each

.. math:: ((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\colon A^{k_0} \times \cdots \times A^{k_{n-1}},

.. math:: f\circ &(g_0, \dots, g_{n-1}))((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\
                 &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).

Not only is this notation tedious, but also it lends itself poorly to computation. To improve upon it, let us first consider the ntuple :math:`(g_0, \dots, g_{n-1})`. This is an ntuple of operations from :math:`\mathrm{Op}(A)`.

If we denote by :math:`g` the function from :math:`\underline{n}` to :math:`\mathrm{Op}(A)` given by :math:`g i = g_i` for each :math:`0\leq i < n`, then :math:`g` inhabits the following dependent function type:

.. math:: \prod_{i : \underline{n}}  ((\underline{k_i} \to A) \to A).

Next, define the function :math:`a` as follows: :math:`a i \colon \underline{k_i} \to A` for each :math:`0\leq i < n` and for each :math:`j\colon \underline{k_i}`, :math:`a i j = a_{ij}`. Then the ntuple of arguments in the expression above can be identified with the tuple :math:`a = (a 0, \dots, a (n-1))` of functions.

Thus :math:`a` has dependent function type :math:`\prod_{i : \underline{n}} (\underline{k_i} \to A)`, and for each :math:`i\colon \underline{n}`, we have :math:`a i j = a_{ij}`.

Now, looking back at the section above, where we defined the fork and eval functions, we can see how to perform general composition using dependent types. If
:math:`g \colon \Pi_{i : \underline{n}} ((\underline{k_i} \to A) \to A)`, and :math:`a \colon \Pi_{i : \underline{n}}(\underline{k_i} \to A)`, then

.. math:: \mathbf{fork} (g) (a) (i) = (g(i), a(i)) : ((\underline{k_i}\to A) \to A) \times (\underline{k_i}\to A)

and :math:`\mathbf{eval} (\mathbf{fork} (g) (a) (i)) = g(i) a(i)` has type :math:`A`.

Observe that the codomain :math:`A` does not depend on :math:`i`, so the types :math:`\Pi_{i:\underline{n}} A` and :math:`\underline{n} \to A` are equivalent. Therefore, :math:`\mathbf{eval} \circ \mathbf{fork} (g) (a)` has type :math:`\underline{n} \to A`.

On the other hand, we have

.. math:: \mathbf{eval}\circ \mathbf{fork} (g) : \prod_{i : \underline{n}}  (\underline{k_i} \to A) \to (\underline{n} \to A).

Thus, if we take an :math:`n`-ary operation, :math:`f\colon (\underline{n} \to A) \to A`, and an :math:`n`-tuple of operations, :math:`g\colon \Pi_{i : \underline{n}} ((\underline{k_i} \to A) \to A)`, then we can *define* the **composition of** :math:`f` **with** :math:`g` as follows:

.. math:: f [g] := f \circ (\mathbf{eval}\circ \mathbf{fork}(g)) : \prod_{i : \underline{n}}(\underline{k_i} \to A) \to A.

Indeed, if :math:`a \colon \Pi_{i : \underline{n}}(\underline{k_i} \to A)`, then :math:`\mathbf{eval}\circ \mathbf{fork}(g)(a)` has type :math:`\underline{n} \to A`, which is the domain type of :math:`f`; therefore, :math:`f (\mathbf{eval}\circ \mathbf{fork}(g) (a))` has type :math:`A`, as desired.

----------------------------------------

.. rubric:: Footnotes

.. [1]
   Using the tuple constructor described in the last section, we could also represent such an operation as :math:`f \colon \mathrm{ntuple} A \to A`, but we prefer to reserve ntuple for instances in which it acts as a functor.
