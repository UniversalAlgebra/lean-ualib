.. math:: \newcommand\FGrp{F_{\mathbf{Grp}}} \newcommand\inj{\mathrm{in}} \newcommand\inji{\mathrm{in}_i} \newcommand\hom{\operatorname{Hom}} \newcommand\hom{\operatorname{Hom}} \newcommand\epi{\operatorname{Epi}} \newcommand\aut{\operatorname{Aut}} \newcommand\mono{\operatorname{Mono}}

Basic Facts
===========

Throught this section,

+ :math:`F` is an endofunctor on **Set**;
+ :math:`\mathbf A = (A, f^A), \; \mathbf B = (B, f^B), \; \mathbf C = (C, f^C)\;` are :ref:`F-algebras <f-algebras>`.

Suppose :math:`F` yields :math:`m` operation symbols and :math:`k_i` is the arity of the :math:`i`-th symbol:

.. math:: F A : \coprod_{i=0}^{m-1}(\underline{k_i} \to A) \quad \text{ and } \quad F B : \coprod_{i=0}^{m-1}(\underline{k_i} \to B).

Let :math:`g, h : \hom(\mathbf A, \mathbf B)` be :ref:`F-algebra homomorphisms <f-algebra-homomorphisms>` from :math:`\mathbf A` to :math:`\mathbf B`:

  :math:`g, h \colon A \to B` are set maps satisfying

  .. math:: g \circ f^A = f^B \circ F g \quad \text{ and } \quad h \circ f^A = f^B \circ F h.

.. index:: ! equalizer

The **equalizer** of :math:`g` and :math:`h` is the set

.. math:: E(g,h) = \{ a : A \mid g(a) = h(a) \}.

Here is a list of basic facts we will need.

.. _fact1:

**1**. :math:`E(g,h)` is a subuniverse of :math:`\mathbf A`.

.. container:: toggle

   .. container:: header

      *Proof*

   Fix arbitrary :math:`0\leq i< m` and :math:`a : \underline{k_i} \to E(g,h)`.

   We show that :math:`g (f^A (\inji a)) = h (f^A (\inji a))`, as this shows that :math:`E(g,h)` is closed under the :math:`i`-th operation of :math:`(A, f^A)`.

   But this is trivial since, by definition of an :ref:`F-algebra homomorphism <f-algebra-homomorphisms>`, we have

   .. math:: (g \circ f^A)(\inji a) = (f^B \circ F g)(\inji a) = (f^B \circ F h)(\inji a) = (h \circ f^A)(\inji a).

.. _fact2:

**2**. If the set :math:`X \subseteq A` generates :math:`\mathbf A` and :math:`g|_X= h|_X`, then :math:`g = h`.

.. container:: toggle

   .. container:: header

      *Proof*

   Suppose the subset :math:`X \subseteq A` generates :math:`(A, f^A)` and suppose :math:`g|_X = h|_X`.

   Fix an arbitrary :math:`a : A`. We show :math:`g(a) = h(a)`.

   Since :math:`X` generates :math:`\mathbf A`, there exists a term :math:`t` and a tuple :math:`x : \rho t \to X` of generators such that :math:`a = t^A x`.

   Therefore, since :math:`F g = F h` on :math:`X`, we have

   .. math:: g(a) = g(t^A x) = (t^B \circ F g)(x) = (t^B \circ F h)(x) = h(t^A x) = h(a).

.. _fact3:

**3**. If :math:`A, B` are finite and :math:`X` generates :math:`\mathbf A`, then :math:`|\hom(\mathbf A, \mathbf B)| \leq |B|^{|X|}`.

.. container:: toggle

   .. container:: header

      *Proof*

   By :ref:`fact 2 <fact2>`, a homomorphism is uniquely determined by its restriction to a generating set.

   If :math:`X` generates :math:`\mathbf A`, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\hom(\mathbf A, \mathbf B)| \leq |B|^{|X|}`.

.. _fact4:

.. (4) Let :math:`g, h` be homomorphisms from :math:`(A, f^A)` to :math:`(B, f^B)` and :math:`(A, f^A)` to :math:`(C,f^C)`, respectively.

**4**. If :math:`g : \epi (\mathbf A, \mathbf B)` and :math:`h : \hom (\mathbf A, \mathbf C)` satisfy :math:`\ker g \subseteq \ker h`, then

  .. math:: \exists k : \hom(\mathbf B, \mathbf C)\ . \, h = k \circ g.

.. container:: toggle

   .. container:: header

      *Proof*

   We define :math:`k : \hom(\mathbf B, \mathbf C)` constructively, as follows:

   Fix :math:`b\colon B`.

   Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} \subseteq A` is nonempty, and since :math:`\ker g \subseteq \ker h`, we see that every element of :math:`g^{-1}\{b\}` is mapped by :math:`h` to a single element of :math:`C`.

   Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a : g^{-1}\{b\}`.

   We define :math:`k(b) = c_b`. Since :math:`b` was arbitrary, :math:`k` is defined on all of :math:`B` in this way.

   Now it's easy to see that :math:`k g = h` by construction.

   Indeed, for each :math:`a \in A`, we have :math:`a \in g^{-1}\{g(a)\}`, so :math:`k(g(a)) = h(a)` by definition.

   To see that :math:`k` is a homomorphism, let there be :math:`m` operation symbols and let :math:`0\leq i< m` be arbitrary.

   Fix :math:`b \colon \underline{k_i} \to B`.

   Since :math:`g` is surjective, for each :math:`i \colon \underline{k_i}`, the subset :math:`g^{-1}\{b(i)\}\subseteq A` is nonempty and is mapped by :math:`h` to a single point of :math:`C` (since :math:`\ker g \subseteq \ker h`.

   Label this point :math:`c_i` and define :math:`c \colon \underline{k_i} \to C` by :math:`c(i) = c_i`.

   We want to show :math:`(f^C \circ F k) (b) = (k \circ f^B)(b).`

   The left hand side is :math:`f^C c`, which is equal to :math:`(h \circ f^A)(a)` for some :math:`a\colon \underline{k_i} \to A`, since :math:`h` is a homomorphism.

   Therefore,

   .. math:: (f^C \circ F k) (b) = (h \circ f^A) (a) = (k \circ g \circ f^A)(a) = (k \circ f^B \circ F g)(a) = (k \circ f^B)(b).


**5**. Let :math:`S = (F, \rho)` be a signature each :math:`f\in F` an :math:`(\rho f)`-ary operation symbol on :math:`A`.

    Define :math:`F_0 := \operatorname{Proj}(A)` and for all :math:`n > 0` in :math:`\omega` let

    .. math:: F_{n+1} := F_n \cup \{ f g \mid f \in F, g \colon \rho f \to (F_n \cap (\rho g \to A)) \}.

    Then :math:`\operatorname{Clo}^{\mathbf A}(F) = \bigcup_n F_n`.

**6**. Let :math:`f` be a similarity type.

    (a) :math:`\mathbf{T}_\rho(X)` is generated by :math:`X`.

    (b) For every algebra :math:`\mathbf A = (A, F)` of type :math:`\rho` and every function :math:`h\colon X \to A` there is a unique homomorphism :math:`g\colon \mathbf{T}_\rho(X) \to (A, f^A)` such that :math:`g\big|_{X} = h`.

.. container:: toggle

   .. container:: header

      *Proof*

   The definition of :math:`\mathbf{T}_\rho(X)` exactly parallels the construction in Theorem 1.14 :cite:`Bergman:2012`. That accounts for the first item.

   For b, define :math:`g(t)` by induction on :math:`|t|`.

   Suppose :math:`|t| = 0`.  Then :math:`t \in X \cup \mathcal{F}_0`.

   If :math:`t \in X` then define :math:`g(t) = h(t)`. For :math:`t \in \mathcal{F}_0`, :math:`g(t) = t^{(A, f^A)}`.

   Note that since :math:`\mathbf A := (A, f^A)` is an algebra of type :math:`f` and :math:`t` is a nullary operation symbol, :math:`t^{(A, f^A)}` is defined.

   For the inductive step, let :math:`|t| = n + 1`. Then :math:`t = f(s_1, \dots, s_k)` for some :math:`f \in \mathcal{F}_k` and :math:`s_1, \dots, s_k` each of height at most :math:`n`. We define :math:`g(t) = f^{(A, f^A)}(g(s_1), \dots, g(s_k))`.

   By its very definition, :math:`g` is a homomorphism. Finally, the uniqueness of :math:`g` follows from Exercise 1.16.6 in :cite:`Bergman:2012`.


**7**. Let :math:`(A, f^A)` and :math:`(B, f^B)` be algebras of type :math:`\rho`.

    (a) For every :math:`n`-ary term :math:`t` and homomorphism :math:`g\colon (A, f^A) \to (B, f^B)`, :math:`g(t^{(A, f^A)}(a_1,\dots, a_n)) = t^{(B, f^B)}(g(a_1),\dots, g(a_n))`.

    (b) For every term :math:`t \in T_\rho(X_\omega)` and every :math:`\theta \in \operatorname{Con}(A, f^A)`, :math:`(A, f^A)\equiv_\theta (B, f^B)\implies t^{(A, f^A)}((A, f^A)) \equiv_\theta t^{(A, f^A)}((B, f^B))`.

    (c) For every subset :math:`Y` of :math:`A`,

        .. math:: \operatorname{Sg}^{(A, f^A)}(Y) = \{ t^{(A, f^A)}(a_1,\dots, a_n) : t \in T(X_n), a_i \in Y, i \leq n < \omega\}.

.. container:: toggle

   .. container:: header

      *Proof*

   The first statement is an easy induction on :math:`|t|`.

   The second statement follows from the first by taking :math:`(B, f^B) = (A, f^A)/\theta` and :math:`g` the canonical homomorphism.

   For the third statement, again by induction on the height of :math:`t`, every subalgebra must be closed under the action of :math:`t^{(A, f^A)}`.

   Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows.
