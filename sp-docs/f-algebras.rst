:math:`\newcommand\FGrp{F_{\mathbf{Grp}}} \newcommand\inj{\mathrm{in}}`

.. index:: ! F-algebra, group, Set, Grp
.. _f-algebras:

F-Algebras
==========

Let :math:`F` be an endofunctor on the category **Set**.

We define an **F-algebra** to be a structure :math:`\mathbf A = (A, f)`, where :math:`f \colon F A \to A`.

Example: **Grp**
----------------

A **group** is an :math:`\FGrp`-algebra where :math:`\FGrp A = 1 + A + A \times A`.

  A definition of a group that is closer to the standard one is the following:

  The *signature* of a group has three operation symbols, :math:`(e, \ ^{-1}, \circ)`.

  - :math:`e` is a nullary ("identity element") operation symbol;
  - :math:`\ ^{-1}` is a unary ("inverse") operation symbol;
  - :math:`\cdot` is a binary ("multiplication") operation symbol.

  Thus, a *group* is an algebraic structure, :math:`\mathbf A = (A, e, \ ^{-1}, \circ)`, where

  - :math:`e : A`;
  - :math:`^{-1} : A \to A`;
  - :math:`\circ : A\times A \to A`.

  If we were to adopt Church's more precise :math:`\lambda` syntax, we could denote a group like this

  .. math:: \mathbf A = (A, e, \lambda x\,. x^{-1}, \lambda x \lambda y\,. x\circ y),

  and then the arity of each operation symbol could be read off immediately! [1]_

  To translate this into the language of F-algebras, observe that an element of the coproduct :math:`\FGrp A` has one of three forms,

  -  :math:`\mathrm{in}_0 1 : 1`, the identity element of the group;
  -  :math:`\mathrm{in}_1 x : A`, an arbitrary element of the group's universe;
  -  :math:`\mathrm{in}_2 (x, y) : A\times A`, an arbitrary pair of elements of the group's universe.

  So, we define and denote the group operations with a single symbol :math:`f \colon \mathbf{F} A \to A`, which acts on elements of the coproduct by pattern matching as follows:

  -  :math:`f\ \mathrm{in}_0 1 = e`, the identity element of the group;
  -  :math:`f\ \mathrm{in}_1 x = x^{-1}`, the group's inverse operation;
  -  :math:`f\ \mathrm{in}_2 (x,y) = x\circ y`, the group's binary operation.

  In `Lean`_, the ``Grp`` type could be implementation like this:

  .. code-block:: lean

      def f : 1 + ℕ + (ℕ × ℕ) → ℕ
      | in₀ 1   := e
      | in₁ x   := x⁻¹
      | in₂ x y := x ∘ y

-------------------------------------------

.. index:: homomorphism
.. index:: ! group homomorphism
.. _f-algebra-homomorphisms:

F-algebra homomorphisms
-----------------------

Let :math:`(A, f)` and :math:`(B, g)` be two groups (i.e., :math:`\FGrp`-algebras).

A **homomorphism** from :math:`(A, f)` to :math:`(B, g)`, denoted by :math:`h\colon (A, f)\to (B, g)`, is a function from :math:`A` to :math:`B` that satisfies the identity

.. math:: h \circ f = g \circ \FGrp h

To make sense of this identity, we must know how the functor :math:`\FGrp` acts on arrows (i.e., homomorphisms, like :math:`h`). It does so as follows:

-  :math:`(\operatorname{F}_{\mathbf{Grp}} h) (\mathrm{in}_0 1) = h(e)`;
-  :math:`(\operatorname{F}_{\mathbf{Grp}} h) (\mathrm{in}_1 x) = (h(x))^{-1}`;
-  :math:`(\operatorname{F}_{\mathbf{Grp}} h) (\mathrm{in}_2 (x,y)) = h(x)\circ h(y)`.

Equivalently,

-  :math:`h \circ f (\inj_0 1) = h (e)` and :math:`g \circ \FGrp h (\inj_0 1) = g (h(e))`;
-  :math:`h \circ f (\inj_1 x) = h (x^{-1})` and :math:`g \circ \FGrp h (\inj_1 x) = g (\inj_1 h(x)) = (h(x))^{-1}`;
-  :math:`h \circ f (\inj_2 (x,y)) = h (x \circ y)` and :math:`g \circ \FGrp h (\inj_2 (x,y)) = g (\inj_2 (h(x),h(y))) = h(x)\circ h(y)`.

So, in this case, the indentity :math:`h \circ f = g \circ \FGrp h` reduces to

-  :math:`h (e^A) = g (h(e))`;
-  :math:`h (x^{-1_A}) = (h(x))^{-1_B}`;
-  :math:`h (x \circ^{A} y)= h(x)\circ^{B} h(y)`,

which are precisely the conditions we would normally verify when checking that :math:`h` is a group homomorphism.

------------------------------------------

.. rubric:: Footnotes

.. [1]
   This should suffice to anger most algebraists.

.. _Lean: https://leanprover.github.io/
