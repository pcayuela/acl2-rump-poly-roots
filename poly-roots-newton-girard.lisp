;; ===========================================================================
;; poly-roots-newton-girard.lisp
;;
;; Newton-Girard identities for lists of numbers, and the elementary
;; symmetric functions e_k computed from the power sums alone.
;;
;; This book is separate from the rump-session development: it only
;; INCLUDES poly-roots-coeffs (for ELEM-SYM, POLY-FROM-ROOTS and
;; CARDANO-VIETA) and changes nothing in it.
;;
;; What is proved (for every list of ACL2 numbers, so, in ACL2(r), also
;; for irrational and complex roots):
;;
;;   1. NEWTON-GIRARD, the identity, for every k >= 0:
;;          k * e_k = sum_{i=1..k} (-1)^(i-1) * e_(k-i) * p_i
;;      where e_k = (elem-sym k lst) and p_i = (power-sum i lst) is the
;;      sum of the i-th powers of the elements of lst.  There is no
;;      hypothesis on the length of lst: for k above the length, e_k = 0
;;      and the identity says that the sum is 0.
;;
;;   2. E-UP-TO-IS-ELEM-LIST: the function E-UP-TO, which computes
;;      (e_k ... e_1 e_0) USING ONLY the power sums p_1..p_k and
;;      division by 1..k (never ELEM-SYM), returns the same list as the
;;      elementary symmetric functions.
;;
;;   3. COEFFICIENT-FROM-POWER-SUMS: with CARDANO-VIETA, each coefficient
;;      of POLY-FROM-ROOTS is, up to sign, the head of E-UP-TO: the
;;      polynomial is determined by the power sums of its roots.
;;
;;   4. Concrete instances: roots (1 2 3), p = (6 14 36), e = (6 11 6),
;;      polynomial s^3 - 6 s^2 + 11 s - 6.
;;
;; What is NOT proved here, and is not claimed:
;;   - nothing about matrices, traces or characteristic polynomials: the
;;     power sums are those of a list of numbers, not of the eigenvalues
;;     of a matrix;
;;   - nothing about polynomials as objects: the fundamental theorem of
;;     symmetric polynomials (every symmetric polynomial is a polynomial
;;     in the e_k) needs a representation of multivariate polynomials
;;     with substitution and permutation of variables, which this book
;;     does not build.
;;
;; Proof of 1, in short: induction on the list, taking off its first
;; element a.  e_j(a.x) = a e_(j-1)(x) + e_j(x) and p_i(a.x) = a^i + p_i(x).
;; Expanding the sum for a.x gives the sum for x (which is k e_k(x) by
;; induction), plus a times the sum for k-1 (which is (k-1) e_(k-1)(x) by
;; induction), plus a telescoping sum that leaves a e_(k-1)(x).  The total
;; is k (a e_(k-1)(x) + e_k(x)) = k e_k(a.x).  The telescoping step is
;; NG-SUM-CONS-PARTIAL.
;;
;; To certify:  (certify-book "poly-roots-newton-girard")
;; It certifies with ACL2 8.7 and with ACL2(r) 8.7(r).
;; ===========================================================================

(in-package "ACL2")

(include-book "poly-roots-coeffs")

;; ---------------------------------------------------------------------------
;; Definitions
;; ---------------------------------------------------------------------------

;; p_i = a_1^i + ... + a_n^i
(defun power-sum (i lst)
  (declare (xargs :guard (and (natp i) (number-listp lst))))
  (if (endp lst)
      0
    (+ (expt (car lst) i) (power-sum i (cdr lst)))))

;; (-1)^(i-1) for i >= 1, by recursion: sign(0) = -1, sign(i) = -sign(i-1).
(defun ng-sign (i)
  (declare (xargs :guard (natp i)))
  (if (zp i) -1 (- (ng-sign (1- i)))))

;; The right-hand side of the identity, summed up to i (i <= k):
;;    sum_{j=1..i} (-1)^(j-1) * e_(k-j)(lst) * p_j(lst)
(defun ng-sum (i k lst)
  (declare (xargs :guard (and (natp i) (natp k) (<= i k) (number-listp lst))))
  (if (zp i)
      0
    (+ (* (ng-sign i) (elem-sym (- k i) lst) (power-sum i lst))
       (ng-sum (1- i) k lst))))

;; ---------------------------------------------------------------------------
;; Auxiliary facts
;; ---------------------------------------------------------------------------

(defthm acl2-numberp-elem-sym
  (acl2-numberp (elem-sym k lst))
  :rule-classes :type-prescription)

(defthm ng-sign-succ
  (implies (natp i)
           (equal (ng-sign (+ 1 i)) (- (ng-sign i)))))

(defthm ng-sign-pos
  (implies (posp i)
           (equal (ng-sign i) (- (ng-sign (+ -1 i))))))

(defthm ng-expt-pos
  (implies (and (posp i) (acl2-numberp a))
           (equal (expt a i) (* a (expt a (+ -1 i))))))

;; ng-expt-pos loops as a general rewrite rule: it is enabled only where
;; it is needed.
(in-theory (disable ng-sign ng-expt-pos))

(defthm ng-sum-of-nil
  (equal (ng-sum i k nil) 0))

(defthm ng-sum-zero
  (implies (zp i) (equal (ng-sum i k lst) 0)))

(defthm elem-sym-cons-pos
  (implies (posp m)
           (equal (elem-sym m (cons a x))
                  (+ (* a (elem-sym (+ -1 m) x)) (elem-sym m x)))))

;; ---------------------------------------------------------------------------
;; The telescoping step: adding a root a to the list, for partial sums
;; (i < k).  The last term is what is left of the telescoping sum.
;; ---------------------------------------------------------------------------

(defthm ng-sum-cons-partial
  (implies (and (natp i) (natp k) (< i k) (acl2-numberp a) (number-listp x))
           (equal (ng-sum i k (cons a x))
                  (+ (ng-sum i k x)
                     (* a (ng-sum i (+ -1 k) x))
                     (* a (elem-sym (+ -1 k) x))
                     (* (ng-sign i) (expt a (+ 1 i))
                        (elem-sym (+ -1 (- k i)) x)))))
  :hints (("Goal" :induct (ng-sum i k x)
                  :in-theory (enable ng-expt-pos))))

;; The full sum (i = k): the last term of the telescoping sum has index 0
;; and cancels against the last term of the sum itself.
(defthm ng-sum-cons-full
  (implies (and (posp k) (acl2-numberp a) (number-listp x))
           (equal (ng-sum k k (cons a x))
                  (+ (ng-sum k k x)
                     (* a (ng-sum (+ -1 k) (+ -1 k) x))
                     (* a (elem-sym (+ -1 k) x)))))
  :hints (("Goal" :expand ((ng-sum k k (cons a x)) (ng-sum k k x))
                  :use ((:instance ng-sum-cons-partial (i (+ -1 k)) (k k))
                        (:instance ng-sign-pos (i k))))))

(defthm ng-sum-full-step
  (implies (and (posp k) (consp lst) (number-listp lst))
           (equal (ng-sum k k lst)
                  (+ (ng-sum k k (cdr lst))
                     (* (car lst) (ng-sum (+ -1 k) (+ -1 k) (cdr lst)))
                     (* (car lst) (elem-sym (+ -1 k) (cdr lst))))))
  :hints (("Goal" :in-theory (disable ng-sum-cons-full)
                  :use ((:instance ng-sum-cons-full
                                   (a (car lst)) (x (cdr lst)))))))

;; ---------------------------------------------------------------------------
;; THEOREM 1: Newton-Girard
;; ---------------------------------------------------------------------------

;; Induction on the list, hypothesis at k and at k-1.
(defun ng-ind (k lst)
  (declare (xargs :measure (len lst)))
  (if (endp lst)
      (nfix k)
    (+ (ng-ind k (cdr lst)) (ng-ind (nfix (+ -1 k)) (cdr lst)))))

(defthm ng-step-arith
  (implies (and (acl2-numberp a) (acl2-numberp e) (acl2-numberp n)
                (equal n (* (+ -1 k) e)))
           (equal (+ (* a e) (* a n)) (* k a e))))

(defthm newton-girard
  (implies (and (natp k) (number-listp lst))
           (equal (ng-sum k k lst)
                  (* k (elem-sym k lst))))
  :hints (("Goal" :induct (ng-ind k lst)
                  :in-theory (disable ng-sum))
          ("Subgoal *1/2.1"
           :use ((:instance ng-step-arith
                            (a (car lst))
                            (e (elem-sym (+ -1 k) (cdr lst)))
                            (n (ng-sum (+ -1 k) (+ -1 k) (cdr lst)))))))
  :rule-classes nil)

;; The first cases, written out.
(defthm newton-girard-1
  (implies (number-listp lst)
           (equal (elem-sym 1 lst) (power-sum 1 lst)))
  :hints (("Goal" :use ((:instance newton-girard (k 1)))
                  :in-theory (enable ng-sum ng-sign))))

(defthm newton-girard-2
  (implies (number-listp lst)
           (equal (* 2 (elem-sym 2 lst))
                  (- (* (elem-sym 1 lst) (power-sum 1 lst))
                     (power-sum 2 lst))))
  :hints (("Goal" :use ((:instance newton-girard (k 2)))
                  :in-theory (enable ng-sum ng-sign))))

;; ---------------------------------------------------------------------------
;; THEOREM 2: e_k from the power sums alone
;; ---------------------------------------------------------------------------

;; sum_{t=1..j} (-1)^(t-1) * (nth (t-1) es) * p_t, where es = (e_(m-1) ... e_0),
;; so that (nth (t-1) es) = e_(m-t).
(defun ng-sum-es (j es lst)
  (declare (xargs :verify-guards nil))
  (if (zp j)
      0
    (+ (* (ng-sign j) (nth (1- j) es) (power-sum j lst))
       (ng-sum-es (1- j) es lst))))

;; (e_k e_(k-1) ... e_1 e_0), computed from the power sums only:
;; e_0 = 1 and e_m = (1/m) sum_{j=1..m} (-1)^(j-1) e_(m-j) p_j.
(defun e-up-to (k lst)
  (declare (xargs :verify-guards nil))
  (if (zp k)
      (list 1)
    (let ((es (e-up-to (1- k) lst)))
      (cons (/ (ng-sum-es k es lst) k) es))))

;; The same list, from ELEM-SYM.
(defun ng-elem-list (k lst)
  (declare (xargs :guard (and (natp k) (number-listp lst))))
  (if (zp k)
      (list 1)
    (cons (elem-sym k lst) (ng-elem-list (1- k) lst))))

(defun ng-nth-ind (k s)
  (if (or (zp k) (zp s)) 0 (ng-nth-ind (1- k) (1- s))))

(defthm nth-ng-elem-list
  (implies (and (natp k) (natp s) (<= s k))
           (equal (nth s (ng-elem-list k lst))
                  (elem-sym (- k s) lst)))
  :hints (("Goal" :induct (ng-nth-ind k s))))

(defthm ng-sum-es-elem-list
  (implies (and (natp j) (natp m) (<= j m) (< 0 m) (number-listp lst))
           (equal (ng-sum-es j (ng-elem-list (+ -1 m) lst) lst)
                  (ng-sum j m lst))))

(defthm e-up-to-is-elem-list
  (implies (and (natp k) (number-listp lst))
           (equal (e-up-to k lst) (ng-elem-list k lst)))
  :hints (("Goal" :induct (e-up-to k lst)
                  :in-theory (disable ng-sum ng-sum-es))
          ("Subgoal *1/2"
           :use ((:instance newton-girard)
                 (:instance ng-sum-es-elem-list (j k) (m k))))))

;; ---------------------------------------------------------------------------
;; THEOREM 3: the coefficients of poly-from-roots from the power sums
;; ---------------------------------------------------------------------------

(defthm car-ng-elem-list
  (equal (car (ng-elem-list m lst)) (elem-sym m lst)))

(defthm coefficient-from-power-sums
  (implies (and (number-listp roots) (natp k) (<= k (len roots)))
           (equal (nth k (poly-from-roots roots))
                  (* (expt -1 (- (len roots) k))
                     (car (e-up-to (- (len roots) k) roots)))))
  :hints (("Goal" :use ((:instance cardano-vieta)
                        (:instance e-up-to-is-elem-list
                                   (k (- (len roots) k)) (lst roots)))
                  :in-theory (disable cardano-vieta e-up-to-is-elem-list))))

;; ---------------------------------------------------------------------------
;; Concrete instances (non-vacuity): roots 1, 2, 3.
;; p_1, p_2, p_3 = 6, 14, 36;  e_3, e_2, e_1, e_0 = 6, 11, 6, 1;
;; s^3 - 6 s^2 + 11 s - 6, as the coefficient list (b_0 b_1 b_2 b_3).
;; ---------------------------------------------------------------------------

(defthm power-sums-of-1-2-3
  (equal (list (power-sum 1 '(1 2 3))
               (power-sum 2 '(1 2 3))
               (power-sum 3 '(1 2 3)))
         '(6 14 36)))

(defthm e-up-to-of-1-2-3
  (equal (e-up-to 3 '(1 2 3)) '(6 11 6 1)))

(defthm poly-from-roots-of-1-2-3
  (equal (poly-from-roots '(1 2 3)) '(-6 11 -6 1)))

;; Roots with a repeated element and a negative one.
(defthm e-up-to-of-2-2-minus-1
  (and (equal (e-up-to 3 '(2 2 -1))
              (ng-elem-list 3 '(2 2 -1)))
       (equal (e-up-to 3 '(2 2 -1)) '(-4 0 3 1))))
