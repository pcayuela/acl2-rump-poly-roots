;; ===========================================================================
;; poly-roots-traces.lisp
;;
;; Characteristic polynomial of an upper-triangular matrix, and its
;; coefficients computed from the traces of the powers of the matrix.
;;
;; This book is self-contained: it needs no linear-algebra book and no RTL.
;; It certifies in ACL2 8.7 and in ACL2(r) 8.7(r).
;;
;; It includes poly-roots-newton-girard (and through it poly-roots-coeffs)
;; and changes nothing in them.
;;
;; What is proved:
;;
;;   1. LDET-UPPER-TRI: the determinant of an upper-triangular n x n matrix
;;      of ACL2 numbers is the product of its diagonal.  The determinant is
;;      LDET, the cofactor (Laplace) expansion along column 0:
;;          det A = sum_i (-1)^i A[i][0] det(minor_{i,0} A).
;;      The proof is induction on n: below the diagonal the column-0 entries
;;      are 0, so only the term i = 0 survives, and the minor (0,0) is again
;;      upper triangular.
;;
;;   2. CHAR-POLY-UPPER-TRI: for an upper-triangular matrix A of ACL2
;;      numbers and every number s,
;;          det(s I - A) = (poly-eval (poly-from-roots diag(A)) s):
;;      the characteristic polynomial is the polynomial whose roots are
;;      the diagonal of A.
;;
;;   3. CTRACE-CMAT-EXPT: tr(A^k) = power-sum of the diagonal, for A upper
;;      triangular (products of upper-triangular matrices are upper
;;      triangular, and their diagonals multiply).
;;
;;   4. CHAR-POLY-FROM-TRACES (main theorem): with E-FROM-TRACES, which
;;      runs the Newton-Girard recursion on tr(A), tr(A^2), ..., each
;;      coefficient of the characteristic polynomial of an upper-triangular
;;      A is (-1)^(n-k) times the head of (e-from-traces (n-k) A n): the
;;      characteristic polynomial is computed from the traces alone.
;;
;; What is NOT proved here, and is not claimed:
;;   - nothing for matrices that are not upper triangular: for a general
;;     matrix, the eigenvalues are not given, and the result needs more
;;     (Faddeev-LeVerrier, or triangularization over the complex numbers);
;;   - the determinant is defined by cofactor expansion along column 0.  It
;;     is not proved here to coincide with the Leibniz formula over
;;     permutations (the definition used by Russinoff's books in
;;     books/projects/linear); for the matrices of this book, the
;;     triangular ones, both are the product of the diagonal.
;;
;; Certification: (certify-book "poly-roots-traces").
;; ===========================================================================

(in-package "ACL2")

(include-book "poly-roots-newton-girard")

;; ======================= matrices as lists of rows
(defun entry (i j a) (nth j (nth i a)))
(in-theory (disable entry))

;; delete row i / delete column 0
(defun del-row (a i)
  (if (consp a)
      (if (zp i) (cdr a) (cons (car a) (del-row (cdr a) (1- i))))
    nil))
(defun del-col0 (a)
  (if (consp a) (cons (cdr (car a)) (del-col0 (cdr a))) nil))
(defun minor0 (a i) (del-col0 (del-row a i)))
(defun cof-sign (i) (if (evenp i) 1 -1))

;; ======================= determinant: cofactor expansion along column 0
;; LDET-SUM adds the terms i, i+1, ..., n-1 of the expansion of an n x n
;; matrix; m = n-1 is the size of the minors.
(mutual-recursion
 (defun ldet (a n)
   (declare (xargs :measure (make-ord 1 (1+ (nfix n)) 0)))
   (if (zp n) 1 (ldet-sum a 0 n (1- n))))
 (defun ldet-sum (a i n m)
   (declare (xargs :measure (make-ord 1 (1+ (nfix m)) (nfix (- (nfix n) (nfix i))))))
   (if (and (natp i) (natp n) (< i n))
       (+ (* (cof-sign i) (entry i 0 a) (ldet (minor0 a i) m))
          (ldet-sum a (1+ i) n m))
     0)))

;; ======================= upper triangular: entry (i,j) = 0 whenever j < i
(defun c-lower-zero-row (a i j)
  (if (zp j) t (and (equal (entry i (1- j) a) 0) (c-lower-zero-row a i (1- j)))))
(defun c-upper-tri-aux (a i)
  (if (zp i) t (and (c-lower-zero-row a (1- i) (1- i)) (c-upper-tri-aux a (1- i)))))
(defun c-upper-tri (a n) (c-upper-tri-aux a n))
(defun cl-prod (l) (if (consp l) (* (car l) (cl-prod (cdr l))) 1))

(defun diag-list (a i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (entry i i a) (diag-list a (1+ i) n))
    nil))

(defthm diag-list-end
  (implies (not (< i n)) (equal (diag-list a i n) nil)))

(defthm c-lower-zero-row-entry
  (implies (and (c-lower-zero-row a i j) (natp j) (natp k) (< k j))
           (equal (entry i k a) 0)))

(defthm c-upper-tri-aux-entry
  (implies (and (c-upper-tri-aux a m) (natp m) (natp i) (natp j) (< j i) (< i m))
           (equal (entry i j a) 0))
  :hints (("Goal" :induct (c-upper-tri-aux a m))))

(defthm c-upper-tri-entry
  (implies (and (c-upper-tri a n) (natp n) (natp i) (natp j) (< j i) (< i n))
           (equal (entry i j a) 0)))

;; From here on, triangularity is used only through C-UPPER-TRI-ENTRY.
(in-theory (disable c-upper-tri))

;; ---- the minor (0,0) of an upper-triangular matrix is upper triangular
(defthm nth-del-col0
  (equal (nth i (del-col0 b)) (cdr (nth i b))))

(defthm nth-cdr-nat
  (implies (natp i) (equal (nth i (cdr x)) (nth (1+ i) x))))

(defthm entry-minor00
  (implies (and (natp i) (natp j))
           (equal (entry i j (minor0 a 0)) (entry (1+ i) (1+ j) a)))
  :hints (("Goal" :in-theory (enable entry minor0 del-row))))

(in-theory (disable minor0))

(defthm c-lower-zero-row-minor
  (implies (and (c-upper-tri a n) (natp n) (natp r) (< r (1- n)) (natp s) (<= s r))
           (c-lower-zero-row (minor0 a 0) r s))
  :hints (("Goal" :induct (c-lower-zero-row (minor0 a 0) r s))))

(defthm c-upper-tri-aux-minor
  (implies (and (c-upper-tri a n) (natp n) (natp i) (<= i (1- n)))
           (c-upper-tri-aux (minor0 a 0) i))
  :hints (("Goal" :induct (c-upper-tri-aux (minor0 a 0) i))))

(defthm c-upper-tri-minor
  (implies (and (c-upper-tri a n) (posp n))
           (c-upper-tri (minor0 a 0) (1- n)))
  :hints (("Goal" :use ((:instance c-upper-tri-aux-minor (i (1- n))))
                  :expand ((c-upper-tri (minor0 a 0) (1- n))))))

(defthm diag-list-minor
  (implies (and (natp n) (natp i) (<= i (1- n)))
           (equal (diag-list (minor0 a 0) i (1- n))
                  (diag-list a (1+ i) n)))
  :hints (("Goal" :induct (diag-list (minor0 a 0) i (1- n)))))

;; ---- below the diagonal the column-0 entries vanish
(defun sum-ind (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n)) (sum-ind (1+ i) n) t))

(defthm ldet-sum-zero
  (implies (and (c-upper-tri a n) (natp n) (posp i))
           (equal (ldet-sum a i n m) 0))
  :hints (("Goal" :induct (sum-ind i n))
          ("Subgoal *1/1" :expand ((ldet-sum a i n m))
                          :use ((:instance c-upper-tri-entry (j 0))))))

(defun n-ind (a n) (if (zp n) a (n-ind (minor0 a 0) (1- n))))

;; ---- THEOREM: the determinant of an upper-triangular matrix
(defthm ldet-upper-tri
  (implies (and (c-upper-tri a n) (natp n))
           (equal (ldet a n) (cl-prod (diag-list a 0 n))))
  :hints (("Goal" :induct (n-ind a n))
          ("Subgoal *1/2" :expand ((ldet a n) (ldet-sum a 0 n (1- n))
                                   (diag-list a 0 n))
                          :use ((:instance ldet-sum-zero (i 1) (m (1- n)))
                                (:instance c-upper-tri-minor)
                                (:instance diag-list-minor (i 0))))))

;; ======================= matrices of numbers
(defun clistnp (x n)
  (if (zp n) (null x) (and (consp x) (acl2-numberp (car x)) (clistnp (cdr x) (1- n)))))
(defun cmatp (a m n)
  (declare (xargs :measure (nfix m)))
  (if (zp m) (null a) (and (consp a) (clistnp (car a) n) (cmatp (cdr a) (1- m) n))))

;; ======================= s*I - A for a numeric matrix A
(defun char-row (s a i j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (if (equal i j) (- s (entry i j a)) (- (entry i j a)))
            (char-row s a i (1+ j) n))
    nil))

(defun char-mat-aux (s a i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (char-row s a i 0 n) (char-mat-aux s a (1+ i) n))
    nil))

(defun char-mat (s a n) (char-mat-aux s a 0 n))

(defun ind-jk (j k)
  (if (zp k) j (ind-jk (1+ j) (1- k))))

(defthm nth-char-row
  (implies (and (natp j) (natp k) (natp n) (< (+ j k) n))
           (equal (nth k (char-row s a i j n))
                  (if (equal i (+ j k)) (- s (entry i (+ j k) a))
                    (- (entry i (+ j k) a)))))
  :hints (("Goal" :induct (ind-jk j k)
                  :expand ((char-row s a i j n)))))

(defthm nth-char-mat-aux
  (implies (and (natp i) (natp k) (natp n) (< (+ i k) n))
           (equal (nth k (char-mat-aux s a i n))
                  (char-row s a (+ i k) 0 n)))
  :hints (("Goal" :induct (ind-jk i k)
                  :expand ((char-mat-aux s a i n)))))

(defthm entry-char-mat
  (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
           (equal (entry i j (char-mat s a n))
                  (if (equal i j) (- s (entry i j a)) (- (entry i j a)))))
  :hints (("Goal" :in-theory (enable entry)
                  :use ((:instance nth-char-mat-aux (i 0) (k i))
                        (:instance nth-char-row (j 0) (k j))))))

(defthm clistnp-char-row
  (implies (and (acl2-numberp s) (natp j) (natp n) (<= j n))
           (clistnp (char-row s a i j n) (- n j)))
  :hints (("Goal" :induct (char-row s a i j n))))

(defthm cmatp-char-mat-aux
  (implies (and (acl2-numberp s) (natp i) (natp n) (<= i n))
           (cmatp (char-mat-aux s a i n) (- n i) n))
  :hints (("Goal" :induct (char-mat-aux s a i n))
          ("Subgoal *1/1" :use ((:instance clistnp-char-row (j 0) (i i))))))

(defthm cmatp-char-mat
  (implies (and (acl2-numberp s) (natp n))
           (cmatp (char-mat s a n) n n))
  :hints (("Goal" :use ((:instance cmatp-char-mat-aux (i 0))))))

(in-theory (disable char-mat))

;; ======================= s*I - A is upper triangular when A is
(defthm c-lower-zero-row-entry
  (implies (and (c-lower-zero-row a i j) (natp j) (natp k) (< k j))
           (equal (entry i k a) 0)))

(defthm c-upper-tri-aux-entry
  (implies (and (c-upper-tri-aux a m) (natp m) (natp i) (natp j) (< j i) (< i m))
           (equal (entry i j a) 0))
  :hints (("Goal" :induct (c-upper-tri-aux a m))))

(defthm c-upper-tri-entry
  (implies (and (c-upper-tri a n) (natp n) (natp i) (natp j) (< j i) (< i n))
           (equal (entry i j a) 0)))

(in-theory (disable c-upper-tri))

(defthm c-lower-zero-row-char-mat
  (implies (and (c-upper-tri a n) (natp n) (natp r) (< r n) (natp k) (<= k r))
           (c-lower-zero-row (char-mat s a n) r k))
  :hints (("Goal" :induct (c-lower-zero-row (char-mat s a n) r k))))

(defthm c-upper-tri-aux-char-mat
  (implies (and (c-upper-tri a n) (natp n) (natp i) (<= i n))
           (c-upper-tri-aux (char-mat s a n) i))
  :hints (("Goal" :induct (c-upper-tri-aux (char-mat s a n) i))))

(defthm c-upper-tri-char-mat
  (implies (and (c-upper-tri a n) (natp n))
           (c-upper-tri (char-mat s a n) n))
  :hints (("Goal" :in-theory (enable c-upper-tri))))

;; ======================= the diagonal of s*I - A
(defthm cl-prod-diag-char-mat
  (implies (and (natp i) (natp n) (<= i n))
           (equal (cl-prod (diag-list (char-mat s a n) i n))
                  (acl2::prod-factors (diag-list a i n) s)))
  :hints (("Goal" :induct (diag-list a i n))))

;; ======================= THEOREM: characteristic polynomial of a triangular matrix
(defthm char-poly-upper-tri
  (implies (and (c-upper-tri a n) (natp n) (acl2-numberp s))
           (equal (ldet (char-mat s a n) n)
                  (acl2::poly-eval (acl2::poly-from-roots (diag-list a 0 n)) s)))
  :hints (("Goal" :use ((:instance ldet-upper-tri (a (char-mat s a n)))))))

;; ======================= numeric matrix product, identity, powers
;; sum_{t<k} a_it * b_tj
(defun dsum (a b i j k)
  (if (zp k) 0 (+ (* (entry i (1- k) a) (entry (1- k) j b)) (dsum a b i j (1- k)))))

(defun mul-row (a b i j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (dsum a b i j n) (mul-row a b i (1+ j) n))
    nil))
(defun mul-mat-aux (a b i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (mul-row a b i 0 n) (mul-mat-aux a b (1+ i) n))
    nil))
(defun cmat* (a b n) (mul-mat-aux a b 0 n))

(defun id-row (i j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (if (equal i j) 1 0) (id-row i (1+ j) n))
    nil))
(defun id-mat-aux (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (id-row i 0 n) (id-mat-aux (1+ i) n))
    nil))
(defun id-mat (n) (id-mat-aux 0 n))

(defun cmat-expt (a k n)
  (if (zp k) (id-mat n) (cmat* a (cmat-expt a (1- k) n) n)))

(defthm nth-mul-row
  (implies (and (natp j) (natp k) (natp n) (< (+ j k) n))
           (equal (nth k (mul-row a b i j n)) (dsum a b i (+ j k) n)))
  :hints (("Goal" :induct (ind-jk j k) :expand ((mul-row a b i j n)))))
(defthm nth-mul-mat-aux
  (implies (and (natp i) (natp k) (natp n) (< (+ i k) n))
           (equal (nth k (mul-mat-aux a b i n)) (mul-row a b (+ i k) 0 n)))
  :hints (("Goal" :induct (ind-jk i k) :expand ((mul-mat-aux a b i n)))))
(defthm entry-cmat*
  (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
           (equal (entry i j (cmat* a b n)) (dsum a b i j n)))
  :hints (("Goal" :in-theory (enable entry)
                  :use ((:instance nth-mul-mat-aux (i 0) (k i))
                        (:instance nth-mul-row (j 0) (k j))))))

(defthm nth-id-row
  (implies (and (natp j) (natp k) (natp n) (< (+ j k) n))
           (equal (nth k (id-row i j n)) (if (equal i (+ j k)) 1 0)))
  :hints (("Goal" :induct (ind-jk j k) :expand ((id-row i j n)))))
(defthm nth-id-mat-aux
  (implies (and (natp i) (natp k) (natp n) (< (+ i k) n))
           (equal (nth k (id-mat-aux i n)) (id-row (+ i k) 0 n)))
  :hints (("Goal" :induct (ind-jk i k) :expand ((id-mat-aux i n)))))
(defthm entry-id-mat
  (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
           (equal (entry i j (id-mat n)) (if (equal i j) 1 0)))
  :hints (("Goal" :in-theory (enable entry)
                  :use ((:instance nth-id-mat-aux (i 0) (k i))
                        (:instance nth-id-row (j 0) (k j))))))

(in-theory (disable cmat* id-mat))

;; dsum for upper-triangular factors (stated on entries, by quantifier-free hypotheses)
(defthm dsum-below-diag
  (implies (and (c-upper-tri a n) (c-upper-tri b n) (natp n)
                (natp i) (natp j) (< j i) (< i n) (natp k) (<= k n))
           (equal (dsum a b i j k) 0))
  :hints (("Goal" :induct (dsum a b i j k))
          ("Subgoal *1/2" :cases ((< (+ -1 k) i)))))

(defthm dsum-diag
  (implies (and (c-upper-tri a n) (c-upper-tri b n) (natp n)
                (natp i) (< i n) (natp k) (<= k n))
           (equal (dsum a b i i k)
                  (if (<= k i) 0 (* (entry i i a) (entry i i b)))))
  :hints (("Goal" :induct (dsum a b i i k))))

;; ======================= products and powers stay upper triangular
(defthm c-lower-zero-row-cmat*
  (implies (and (c-upper-tri a n) (c-upper-tri b n) (natp n)
                (natp r) (< r n) (natp k) (<= k r))
           (c-lower-zero-row (cmat* a b n) r k))
  :hints (("Goal" :induct (c-lower-zero-row (cmat* a b n) r k))))
(defthm c-upper-tri-aux-cmat*
  (implies (and (c-upper-tri a n) (c-upper-tri b n) (natp n) (natp i) (<= i n))
           (c-upper-tri-aux (cmat* a b n) i))
  :hints (("Goal" :induct (c-upper-tri-aux (cmat* a b n) i))))
(defthm c-upper-tri-cmat*
  (implies (and (c-upper-tri a n) (c-upper-tri b n) (natp n))
           (c-upper-tri (cmat* a b n) n))
  :hints (("Goal" :in-theory (enable c-upper-tri))))

(defthm c-lower-zero-row-id-mat
  (implies (and (natp n) (natp r) (< r n) (natp k) (<= k r))
           (c-lower-zero-row (id-mat n) r k))
  :hints (("Goal" :induct (c-lower-zero-row (id-mat n) r k))))
(defthm c-upper-tri-aux-id-mat
  (implies (and (natp n) (natp i) (<= i n))
           (c-upper-tri-aux (id-mat n) i))
  :hints (("Goal" :induct (c-upper-tri-aux (id-mat n) i))))
(defthm c-upper-tri-id-mat
  (implies (natp n) (c-upper-tri (id-mat n) n))
  :hints (("Goal" :in-theory (enable c-upper-tri))))

(defthm c-upper-tri-cmat-expt
  (implies (and (c-upper-tri a n) (natp n))
           (c-upper-tri (cmat-expt a k n) n)))

(defthm diag-cmat-expt
  (implies (and (c-upper-tri a n) (natp n) (natp i) (< i n) (natp k))
           (equal (entry i i (cmat-expt a k n)) (expt (entry i i a) k)))
  :hints (("Goal" :induct (cmat-expt a k n))))

;; ======================= traces
(defun ctrace (a i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (+ (entry i i a) (ctrace a (1+ i) n))
    0))

(defthm ctrace-cmat-expt
  (implies (and (c-upper-tri a n) (natp n) (natp i) (natp k))
           (equal (ctrace (cmat-expt a k n) i n)
                  (acl2::power-sum k (diag-list a i n))))
  :hints (("Goal" :induct (diag-list a i n))))

(in-theory (disable cmat-expt))

;; ======================= e_k from the traces of the powers of A
;; Same recursion as ACL2::E-UP-TO, with p_j replaced by tr(A^j).
(defun tr-sum-es (j es a n)
  (if (zp j)
      0
    (+ (* (acl2::ng-sign j) (nth (1- j) es) (ctrace (cmat-expt a j n) 0 n))
       (tr-sum-es (1- j) es a n))))

(defun e-from-traces (k a n)
  (if (zp k)
      (list 1)
    (let ((es (e-from-traces (1- k) a n)))
      (cons (/ (tr-sum-es k es a n) k) es))))

(defthm tr-sum-es-is-ng-sum-es
  (implies (and (c-upper-tri a n) (natp n))
           (equal (tr-sum-es j es a n)
                  (acl2::ng-sum-es j es (diag-list a 0 n)))))

(defthm e-from-traces-is-e-up-to
  (implies (and (c-upper-tri a n) (natp n))
           (equal (e-from-traces k a n)
                  (acl2::e-up-to k (diag-list a 0 n))))
  :hints (("Goal" :induct (e-from-traces k a n)
                  :in-theory (disable tr-sum-es acl2::ng-sum-es))))

(defthm len-diag-list
  (implies (and (natp i) (natp n) (<= i n))
           (equal (len (diag-list a i n)) (- n i))))

(defthm acl2-numberp-nth-clistnp
  (implies (and (clistnp x n) (natp n) (natp j) (< j n))
           (acl2-numberp (nth j x))))

(defthm clistnp-nth-cmatp
  (implies (and (cmatp a m n) (natp m) (natp i) (< i m))
           (clistnp (nth i a) n)))

(defthm acl2-numberp-entry-cmatp
  (implies (and (cmatp a m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
           (acl2-numberp (entry i j a)))
  :hints (("Goal" :in-theory (enable entry))))

(defthm number-listp-diag-list
  (implies (and (cmatp a n n) (natp i) (natp n))
           (acl2::number-listp (diag-list a i n)))
  :hints (("Goal" :induct (diag-list a i n))))


;; ======================= MAIN THEOREM
;; For an upper-triangular n x n matrix A of ACL2 numbers:
;;  (1) det(sI - A) is the polynomial whose roots are the diagonal of A;
;;  (2) its k-th coefficient is (-1)^(n-k) e_(n-k), where e_(n-k) is computed
;;      ONLY from the traces tr(A), tr(A^2), ..., tr(A^(n-k)).
(defthm char-poly-from-traces
  (implies (and (cmatp a n n) (posp n) (c-upper-tri a n)
                (acl2-numberp s) (natp k) (<= k n))
           (and (equal (ldet (char-mat s a n) n)
                       (acl2::poly-eval (acl2::poly-from-roots (diag-list a 0 n)) s))
                (equal (nth k (acl2::poly-from-roots (diag-list a 0 n)))
                       (* (expt -1 (- n k))
                          (car (e-from-traces (- n k) a n))))))
  :hints (("Goal" :use ((:instance acl2::coefficient-from-power-sums
                                   (acl2::roots (diag-list a 0 n)) (acl2::k k))
                        (:instance char-poly-upper-tri)))))
