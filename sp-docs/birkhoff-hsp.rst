:math:`\def\inj{\mathrm{in}}` :math:`\def\inji{\mathrm{in}_i}` #

Notation
========

The symbols :math:`\mathbb{N}`, :math:`\omega`, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m \colon \mathbb N` and say ":math:`m` has type :math:`\mathbb N`." (For the reader unfamiliar with type theory, it's safe in the beginning to think of this as meaning :math:`m\in \mathbb N`.)

For :math:`m \colon \mathbb N`, we denote and define :math:`\underline{m} = \\{0, 1, \dots, m-1\\}`. Let :math:`a = (a_0, a_1, \dots, a_{m-1})` be an `mtuple <composition>`__ of elements from :math:`A`.

(As explained in `the post on composition of
operations <composition>`__, the tuple :math:`a` may be identified with
a function of type :math:`\underline{m} \to A`, where
:math:`a(i) = a_i`, for each :math:`i<m`.)

If :math:`h \colon A \to A`, then :math:`h\circ a : \underline{m} \to A`
is the function whose :math:`i`-th coordinate is
:math:`(h\circ a)(i) = h(a(i)) = h(a_i)`, and we may formally identify
the function :math:`h \circ a : \underline{m} \to A` with its "image
tuple" :math:`(h(a_0), h(a_1), \dots, h(a_{m-1}))`.

A **signature** :math:`S = (F, \rho)` consists of a set :math:`F` of
operation symbols and a function :math:`\rho \colon F \to \mathbb{N}`.
We call :math:`\rho f` the **arity** of the symbol :math:`f`.

If :math:`A` is a set and :math:`f` is a :math:`\rho f`-ary operation on
:math:`A`, then we may write :math:`f \colon A^{\rho f} \to A`. On the
other hand, as the natural number :math:`\rho f` denotes the set
:math:`\\{0, 1, \dots, \rho f -1\\}`, a function
:math:`a \colon \rho f \to A` can be identified with its graph, which is
simply a :math:`\rho f`-tuple of elements from :math:`A`; that is,
:math:`a i : A`, for each :math:`i: \rho f`. Then, by identifying the
:math:`\rho f`-th power :math:`A^{\rho f}` with the type
:math:`\rho f \to A` of functions from
:math:`\\{0, 1, \dots, \rho f -1\\}` to :math:`A`, we thus identify the
function type :math:`A^{\rho f} \to A` with the type
:math:`(\rho f \to A) \to A`.

| **Examples.**
| a. If :math:`g \colon (\underline{m} \to A) \to A` is an
  :math:`\underline{m}`-ary operation on :math:`A` and if
  :math:`a : \underline{m} \to A`, then
  :math:`g a = g(a_0, a_1, \dots, a_{m-1})` has type :math:`A`.
| b. If :math:`f \colon (\rho f \to B) \to B` is a :math:`\rho f`-ary
  operation on :math:`B`, if :math:`a \colon \rho f \to A` is a
  :math:`\rho f`-tuple on :math:`A`, and if :math:`h \colon A \to B`,
  then of course :math:`h \circ a \colon \rho f \to B`, so
  :math:`f (h \circ a)` has type :math:`B`.

**Generalized composition.** We summarize in a single sentence the final
result of `our previous post on *general composition* <composition>`__.
If :math:`f\colon (\underline n \to A) \to A` and if
:math:`g : \Pi_{i:\underline{n}} (\underline{k_i} \to A) \to A` and
:math:`a : \Pi_{i : \underline{n}}(\underline{k_i} \to A)`, then
:math:`\mathbf{eval}\circ \mathbf{fork}(g)(a)` has type
:math:`\underline{n} \to A`, which is the domain type of :math:`f`;
therefore, :math:`f \circ (\mathbf{eval}\circ \mathbf{fork}(g) (a))` has
type :math:`A`, as desired. See `the post on general
composition <composition>`__ for details.

We summarize in a single sentence the final result of `our previous post
on *general composition* <composition>`__. If
:math:`f\colon (\underline n \to A) \to A` and if
:math:`g : \Pi_{i:\underline{n}} (\underline{k_i} \to A) \to A` and
:math:`a : \Pi_{i : \underline{n}}(\underline{k_i} \to A)`, then
:math:`\mathbf{eval}\circ \mathbf{fork}(g)(a)` has type
:math:`\underline{n} \to A`, which is the domain type of :math:`f`;
therefore, :math:`f \circ (\mathbf{eval}\circ \mathbf{fork}(g) (a))` has
type :math:`A`, as desired. See `the post on general composition
post <composition>`__ for details.


Birkhoff's Theorem
------------------

Let :math:`\rho` be a similarity type. An **identity of type**
:math:`\rho` is an ordered pair of terms, written :math:`p \approx q`,
from :math:`T_\rho(X_\omega)`. Let :math:`(A, f^A)` be an algebra of
type :math:`\rho`. We say that :math:`(A, f^A)` satisfies
:math:`p\approx q` if :math:`p^{(A, f^A)} = q^{(A, f^A)}`. In this
situation, we write :math:`(A, f^A) \models p \approx q`. If
:math:`\mathcal{K}` is a class of algebras of type :math:`\rho`, we
write :math:`\mathcal{K} \models p \approx q` if
:math:`\forall (A, f^A) \in \mathcal{K}`,
:math:`(A, f^A) \models p \approx q`. Finally, if :math:`\Sigma` is a
set of equations, we write :math:`\mathcal{K} \models \Sigma` if every
member of :math:`\mathcal{K}` satisfies every member of :math:`\Sigma`.

Let :math:`\mathcal{K}` be a class of algebras and :math:`\Sigma` a set
of equations, each of similarity type :math:`\rho`. We define
:math:`\operatorname{Id}(\mathcal{K}) = \\{p \approx q : \mathcal{K} \models p \approx q\\}`
and
:math:`\operatorname{Mod}(\Sigma) = \\{ (A, f^A) : (A, f^A) \models \Sigma \\}`.
Classes of the form :math:`\operatorname{Mod}(\Sigma)` are called
**equational classes**, and :math:`\Sigma` is called an **equational
base** or an **axiomatization** of the class.
:math:`\operatorname{Mod}(\Sigma)` is called the class of **models** of
:math:`\Sigma`. Dually, a set of identities of the form
:math:`\operatorname{Id}(\mathcal{K})` is called an **equational
theory**.

1. For every class :math:`\mathcal{K}`, each of the classes
   :math:`\mathbf{S}(\mathcal{K})`, :math:`\mathbf{H}(\mathcal{K})`,
   :math:`\mathbf{P}(\mathcal{K})`, and :math:`\mathbf{V}(\mathcal{K})`
   satisfies exactly the same identities as does :math:`\mathcal{K}`.

   (exercise)

2. :math:`\mathcal{K} \models p \approx q` if and only if for every
   :math:`(A, f^A) \in \mathcal{K}` and every
   :math:`h\in \operatorname{Hom}(\mathbf{T}(X_\omega),(A, f^A))}}`, we
   have :math:`h(p) = h(q)`.

   **Proof.** First assume that :math:`\mathcal{K} \models p\approx q`.
   Pick :math:`(A, f^A)` and :math:`h` as in the theorem. Then
   :math:`(A, f^A) \models p\approx q \implies p^{(A, f^A)} = q^{(A, f^A)} \implies p^{(A, f^A)}(h(x_1), \dots, h(x_n)) = q^{(A, f^A)}(h(x_1), \dots, h(x_n))`.
   Since :math:`h` is a homomorphism, we get
   :math:`h(p^{(A, f^A)}(x_1, \dots, x_n)) = h(q^{(A, f^A)}(x_1, \dots, x_n))`,
   i.e., :math:`h(p) = h(q)`.

   To prove the converse we must take any
   :math:`(A, f^A) \in \mathcal{K}` and :math:`a_1, \dots, a_n \in A`
   and show that
   :math:`p^{(A, f^A)}(x_1, \dots, x_n) = q^{(A, f^A)}(x_1, \dots, x_n)`.
   Let :math:`h_0 \colon X_\omega \to A` be a function with
   :math:`h_0(x_i) = a_i` for :math:`i\leq n`. By Theorem 4.21 (Bergman,
   2012), :math:`h_0` extends to a homomorphism :math:`h` from
   :math:`\mathbf{T}(X_\omega)` to :math:`(A, f^A)`. By assumption
   :math:`h(p) = h(q)`. Since
   :math:`h(p) = h(p^{(A, f^A)}(x_1, \dots, x_n)) = p^{(A, f^A)}(h(x_1), \dots, h(x_n)) = p^{(A, f^A)}(a_1,\dots, a_n)`
   (and similarly for :math:`q`) the result follows.

3. Let :math:`\mathcal{K}` be a class of algebras and
   :math:`p \approx q` an equation. The following are equivalent.

   a. :math:`\mathcal{K} \models p\approx q`.

   b. :math:`(p,q)` belongs to the congruence
      :math:`\lambda_{\mathcal{K}}` on :math:`\mathbf{T}(X_\omega)`.

   c. :math:`\mathbf{F}_{\mathcal{K}}(X_\omega) \models p\approx q`.

   **Proof.** We shall show (a) :math:`\implies` (c) :math:`\implies`
   (b) :math:`\implies` (a). Throughout the proof we write
   :math:`\mathbf{F}` for :math:`\mathbf{F}_{\mathcal{K}}(X_\omega)`,
   :math:`\mathbf{T}` for :math:`\mathbf{T}(X_\omega)` and
   :math:`\lambda` for :math:`\lambda_{\mathcal{K}}`.

   Recall that
   :math:`\mathbf{F} = \mathbf{T}/\lambda \in \mathbf{S}\mathbf{P}(\mathcal{K})`.
   From (a) and Lemma 4.36 (Bergman, 2012) we get
   :math:`\mathbf{S}\mathbf{P}(\mathcal{K}) \models p \approx q`. Thus
   (c) holds.

   From (c),
   :math:`p^{\mathbf{F}}(\bar{x}_1,\dots, \bar{x}_n) = q^{\mathbf{F}}(\bar{x}_1,\dots, \bar{x}_n)`
   where :math:`\bar{x}_i = x_i/\lambda`. From the definition of
   :math:`\mathbf{F}`,
   :math:`p^{\mathbf{T}}(x_1,\dots, x_n) \equiv_\lambda q^{\mathbf{T}}(x_1,\dots, x_n)`
   from which (b) follows since
   :math:`p = p^{\mathbf{T}}(x_1,\dots, x_n)` and
   :math:`q = q^{\mathbf{T}}(x_1,\dots, x_n)`.

   Finally assume (b). We wish to apply Lemma 4.37. Let
   :math:`(A, f^A) \in \mathcal{K}` and
   :math:`h \in \operatorname{Hom}(\mathbf{T},(A, f^A))}}`. Then
   :math:`\mathbf{T}/\ker h \in \mathbf{S}((A, f^A)) \subseteq \mathbf{S}(\mathcal{K})`
   so :math:`\ker h \supseteq \lambda`. Then (b) implies that
   :math:`h(p) = h(q)` hence (a) holds, completing the proof.

   **Remark.** The last result tells us that we can determine whether an
   identity is true in a variety by consulting a particular algebra,
   namely :math:`\mathbf{F}(X_\omega)`. Sometimes it is convenient to
   work with algebras free on other generating sets besides
   :math:`X_\omega`. The following corollary takes care of that for us.

4. Let :math:`\mathcal{K}` be a class of algebras, :math:`p` and
   :math:`q` :math:`n`-ary terms, :math:`Y` a set and
   :math:`y_1, \dots, y_n` distinct elements of :math:`Y`. Then
   :math:`\mathcal{K} \models p \approx q` if and only if
   :math:`p^{\mathbf{F}_{\mathcal{K}}(Y)}(y_1, \dots, y_n) = q^{\mathbf{F}_{\mathcal{K}}(Y)}(y_1, \dots, y_n)`.
   In particular, :math:`\mathcal{K} \models p \approx q` if and only if
   :math:`\mathbf{F}_{\mathcal{K}}(X_n)\models p \approx q`.

   **Proof.** Since
   :math:`\mathbf{F}_{\mathcal{K}}(Y)\in \mathbf{S}\mathbf{P}(\mathcal{K})`,
   the left-to-right direction uses the same argument as in Theorem 4.38
   (Bergman, 2012) (Result 3 in this section). So assume that
   :math:`p^{\mathbf{F}_{\mathcal{K}}(Y)}(y_1, \dots, y_n) = q^{\mathbf{F}_{\mathcal{K}}(Y)}(y_1, \dots, y_n)`.
   To show that :math:`\mathcal{K} \models p \approx q`, let
   :math:`(A, f^A) \in \mathcal{K}` and :math:`a_1`, :math:`\dots`,
   :math:`a_n \in A`. We must show
   :math:`p^{(A, f^A)}(a_1, \dots, a_n) = q^{(A, f^A)}(a_1, \dots, a_n)`.

   There is a homomorphism
   :math:`h\colon \mathbf{F}_{\mathcal{K}}(Y) \to (A, f^A)` such that
   :math:`h(y_i) = a_i` for :math:`i \leq n`. Then

   .. raw:: latex

      \begin{align*}  p^{(A, f^A)}(a_1, \dots, a_n) &= p^{(A, f^A)}(h (y_1), \dots, h (y_n)) = h(p^{\mathbf{F}_{\mathcal{K}}(Y)}(y_1, \dots, y_n))\\ &= h(q^{\mathbf{F}_{\mathcal{K}}(Y)}(y_1, \dots, y_n)) = q^{(A, f^A)}(h(y_1), \dots, h(y_n))\\ &= q^{(A, f^A)}(a_1, \dots, a_n).\end{align*}

   It follows from Lemma 4.36 (Result 1 of this section) that every
   equational class is a variety. The converse is Birkhoff’s Theorem.

**Theorem** (Bergman, Thm 4.41) Every variety is an equational class.

**Proof.** Let :math:`\mathcal{W}` be a variety. We must find a set of
equations that axiomatizes :math:`\mathcal{W}`. The obvious choice is to
use the set of all equations that hold in :math:`\mathcal{W}`. To this
end, take :math:`\Sigma = \operatorname{Id}(\mathcal{W})`. Let
:math:`\overline{\mathcal{W}} = \operatorname{Mod}(\Sigma)`. Clearly,
:math:`\mathcal{W} \subseteq \overline{\mathcal{W}}`. We shall prove the
reverse inclusion.

Let :math:`(A, f^A) \in \overline{\mathcal{W}}` and :math:`Y` a set of
cardinality :math:`\max(|A|, |\omega|)`. Choose a surjection
:math:`h_0\colon Y \to A`. By Theorem [thm:4.21], :math:`h_0` extends to
a (surjective) homomorphism :math:`h \colon \mathbf{T}(Y) \to (A, f^A)`.
Furthermore, since
:math:`\mathbf{F}_{\mathcal{W}}(Y) = \mathbf{T}(Y)/\Theta_{\mathcal{W}}`,
there is a surjective homomorphism
:math:`g \colon \mathbf{T}(Y) \to \mathbf{F}_{\mathcal{W}}`.

We claim that :math:`\ker g \subseteq \ker h`. If the claim is true then
by Lemma [ex:1.26.8] there is a map
:math:`f\colon \mathbf{F}_{\mathcal{W}}(Y) \to (A, f^A)` such that
:math:`f {\circ}}g = h`. Since :math:`h` is surjective, so is :math:`f`.
Hence
:math:`(A, f^A) \in \mathbf{H}(\mathbf{F}_{\mathcal{W}}(Y)) \subseteq \mathcal{W}`
completing the proof.

Let :math:`u,v \in T(Y)` and assume that :math:`g(u) = g(v)`. Since
:math:`\mathbf{T}(Y)` is generated by :math:`Y`, by Theorem [thm:4.21],
there is an integer :math:`n`, terms :math:`p, q \in T(X_n)`, and
:math:`y_1`, :math:`\dots`, :math:`y_n \in Y` such that
:math:`u = p^{\mathbf{T}(Y)}(y_1,\dots, y_n)` and
:math:`v = q^{\mathbf{T}(Y)}(y_1,\dots, y_n)`, by Theorem [thm:4.32].
Applying the homomorphism :math:`g`,

.. math:: p^{\mathbf{F}_{\mathcal{W}}(Y)}(y_1,\dots, y_n) = g(u) = g(v) = q^{\mathbf{F}_{\mathcal{W}}(Y)}(y_1,\dots, y_n).

Then by Result 4 above (Corollary 4.39, Bergman, 2012),
:math:`\mathcal{W} \models p \approx q`, hence
:math:`(p \approx q) \in \Sigma`. Since
:math:`(A, f^A) \in \overline{\mathcal{W}} = \operatorname{Mod}(\Sigma)`,
we get :math:`(A, f^A) \models p \approx q`. Therefore,

.. math:: h(u) = p^{(A, f^A)}(h_0(y_1), \dots, h_0(y_n)) = q^{(A, f^A)}(h_0(y_1), \dots, h_0(y_n)) = h(v),

 as desired.

.. raw:: html

   <!-- [inputs/refs.bib]{} @book [MR2839398, AUTHOR = [Bergman, Clifford]{},
   TITLE = [Universal algebra]{}, SERIES = [Pure and Applied Mathematics
   (Boca Raton)]{}, VOLUME = [301]{}, NOTE = [Fundamentals and selected
   topics]{}, PUBLISHER = [CRC Press, Boca Raton, FL]{}, YEAR = [2012]{},
   PAGES = [xii+308]{}, ISBN = [978-1-4398-5129-6]{}, MRCLASS = [08-02
   (06-02 08A40 08B05 08B10 08B26)]{}, MRNUMBER = [2839398
   (2012k:08001)]{}, MRREVIEWER = [Konrad P. Pi[ó]{}ro]{}, ]{} -->
