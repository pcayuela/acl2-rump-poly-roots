;; ===========================================================================
;; poly-roots-leibniz.lisp
;;
;; The determinant of poly-roots-traces (cofactor expansion along column 0,
;; LDET) is Leibniz's determinant: the sum, over all permutations, of the
;; signed products of entries.
;;
;; cert_param: (non-acl2r)
;;
;; This book is ACL2-only: it uses David Russinoff's linear-algebra books
;; (books/projects/linear: ring, rmat, rdet), which depend on the RTL
;; library, and the RTL library does not certify under ACL2(r) (its
;; arithmetic assumes that every non-complex number is rational).
;; poly-roots-traces itself does not use them and certifies in both.
;;
;; What is proved (package DM, portcullis in poly-roots-leibniz.acl2):
;;
;;   1. CEXPAND-COL-CDET: Russinoff's theorem EXPAND-RDET-COL-RDET
;;      (cofactor expansion along any column equals the determinant, whose
;;      definition RDET is the Leibniz formula over (slist n)), instantiated
;;      to ACL2 numbers by functional instantiation.  CDET, CCOFACTOR,
;;      CEXPAND-COL are the numeric copies of RDET, RDET-COFACTOR,
;;      EXPAND-RDET-COL that functional instantiation requires.
;;
;;   2. MINOR-I0-IS-MINOR0: Russinoff's minor (MINOR i 0 a) is the minor
;;      (ACL2::MINOR0 a i) used by LDET.
;;
;;   3. LDET-IS-LEIBNIZ (main theorem): for every n x n matrix of ACL2
;;      numbers, (ldet a n) = (cdet a n).  Induction on n; the step uses 1
;;      and 2 and the commutativity of the sum, which Russinoff adds from
;;      the last row down and LDET from row 0 up.
;;
;;   4. CHAR-POLY-FROM-TRACES-LEIBNIZ: the main theorem of poly-roots-traces
;;      with Leibniz's determinant in place of LDET.
;;
;; Nothing is changed in poly-roots-coeffs, poly-roots-newton-girard or
;; poly-roots-traces.
;;
;; Certification: (certify-book "poly-roots-leibniz") with the portcullis in
;; poly-roots-leibniz.acl2.  Certifying from scratch also certifies
;; Russinoff's books and part of RTL (several minutes).
;; ===========================================================================

(in-package "DM")

(include-book "projects/linear/rdet" :dir :system)
(include-book "poly-roots-traces")

;; ======================= Russinoff's determinant, instantiated to ACL2 numbers
;; (ring := ACL2 numbers with +, *, 0, 1, -).  Same copies as in the book
;; poly-roots-traces of branch traces-v4.
(defun cdet-prod (a p n)
  (if (zp n) 1 (* (cdet-prod a p (1- n)) (entry (1- n) (nth (1- n) p) a))))
(defun cdet-term (a p n)
  (if (even-perm-p p n) (cdet-prod a p n) (- (cdet-prod a p n))))
(defun cdet-sum (a l n)
  (if (consp l) (+ (cdet-term a (car l) n) (cdet-sum a (cdr l) n)) 0))
(defun cdet (a n) (cdet-sum a (slist n) n))
(defun ccofactor (i j a n)
  (if (evenp (+ i j)) (cdet (minor i j a) (1- n)) (- (cdet (minor i j a) (1- n)))))
(defun cexpand-col-aux (a i j n)
  (if (zp i) 0
    (+ (* (entry (1- i) j a) (ccofactor (1- i) j a n))
       (cexpand-col-aux a (1- i) j n))))
(defun cexpand-col (a j n) (cexpand-col-aux a n j n))

;; ---- Russinoff's cofactor expansion by a column, for numbers
(defthm cexpand-col-cdet
  (implies (and (acl2::cmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (cexpand-col a k n) (cdet a n)))
  :hints (("Goal" :by (:functional-instance expand-rdet-col-rdet
                        (rp acl2-numberp) (r+ binary-+) (r* binary-*)
                        (r0 (lambda () 0)) (r1 (lambda () 1)) (r- unary--)
                        (rlistnp acl2::clistnp) (rmatp acl2::cmatp)
                        (rdet cdet) (rdet-sum cdet-sum) (rdet-term cdet-term)
                        (rdet-prod cdet-prod)
                        (rdet-cofactor ccofactor)
                        (expand-rdet-col cexpand-col)
                        (expand-rdet-col-aux cexpand-col-aux)))
          ("Subgoal 1" :in-theory (enable rdet-term rdet rdet-cofactor expand-rdet-col))))

;; ---- numeric versions of Russinoff's lemmas on minors
(defthm cmatp-minor
  (implies (and (acl2::cmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (acl2::cmatp (minor i j a) (1- n) (1- n)))
  :hints (("Goal" :by (:functional-instance rmatp-minor
                        (rp acl2-numberp) (r+ binary-+) (r* binary-*)
                        (r0 (lambda () 0)) (r1 (lambda () 1)) (r- unary--)
                        (rlistnp acl2::clistnp) (rmatp acl2::cmatp)))))

(defthm row-cmat-minor
  (implies (and (acl2::cmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)))
           (equal (nth r (minor i j a))
                  (delete-nth j (nth (if (< r i) r (1+ r)) a))))
  :hints (("Goal" :by (:functional-instance row-rmat-minor
                        (rp acl2-numberp) (r+ binary-+) (r* binary-*)
                        (r0 (lambda () 0)) (r1 (lambda () 1)) (r- unary--)
                        (rlistnp acl2::clistnp) (rmatp acl2::cmatp)))))

(defthm len-cmatp
  (implies (and (natp m) (acl2::cmatp a m n)) (equal (len a) m))
  :hints (("Goal" :in-theory (enable acl2::cmatp))))

(defthm true-listp-cmatp
  (implies (acl2::cmatp a m n) (true-listp a))
  :hints (("Goal" :in-theory (enable acl2::cmatp))))

(defun del-row-ind (a r i)
  (if (or (zp i) (zp r)) a (del-row-ind (cdr a) (1- r) (1- i))))

(defthm nth-del-row
  (implies (and (natp r) (natp i))
           (equal (nth r (acl2::del-row a i))
                  (nth (if (< r i) r (1+ r)) a)))
  :hints (("Goal" :induct (del-row-ind a r i)
                  :in-theory (enable acl2::del-row))))

(defthm len-del-row
  (implies (and (natp i) (< i (len a)))
           (equal (len (acl2::del-row a i)) (1- (len a))))
  :hints (("Goal" :in-theory (enable acl2::del-row))))

(defthm len-del-col0
  (equal (len (acl2::del-col0 a)) (len a)))

(defthm true-listp-del-col0
  (true-listp (acl2::del-col0 a)))

(defthm true-listp-del-row
  (implies (true-listp a) (true-listp (acl2::del-row a i)))
  :hints (("Goal" :in-theory (enable acl2::del-row))))

;; ---- two lists are equal when their first k elements agree (by induction)
(defun all-nth-eq (x y k)
  (if (zp k)
      t
    (and (equal (nth (1- k) x) (nth (1- k) y))
         (all-nth-eq x y (1- k)))))

(defthm all-nth-eq-nth
  (implies (and (all-nth-eq x y k) (natp k) (natp r) (< r k))
           (equal (nth r x) (nth r y)))
  :hints (("Goal" :induct (all-nth-eq x y k))))

(defthm all-nth-eq-cdr
  (implies (and (all-nth-eq x y (1+ k)) (natp k))
           (all-nth-eq (cdr x) (cdr y) k)))

(defun cdr-cdr-ind (x y)
  (if (or (atom x) (atom y)) 0 (cdr-cdr-ind (cdr x) (cdr y))))

(defthm equal-from-all-nth-eq
  (implies (and (true-listp x) (true-listp y)
                (equal (len x) (len y))
                (all-nth-eq x y (len x)))
           (equal x y))
  :hints (("Goal" :induct (cdr-cdr-ind x y))
          ("Subgoal *1/2" :use ((:instance all-nth-eq-cdr (k (len (cdr x))))
                                (:instance all-nth-eq-nth (r 0) (k (len x))))))
  :rule-classes nil)

;; ---- the minor (i,0) of Russinoff is the minor of poly-roots-traces
(defthm all-nth-eq-minors
  (implies (and (acl2::cmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (natp k) (<= k (1- n)))
           (all-nth-eq (minor i 0 a) (acl2::minor0 a i) k))
  :hints (("Goal" :induct (all-nth-eq (minor i 0 a) (acl2::minor0 a i) k)
                  :in-theory (enable acl2::minor0))))

(defthm len-minor
  (implies (and (acl2::cmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (equal (len (minor i j a)) (1- n)))
  :hints (("Goal" :use ((:instance cmatp-minor)
                        (:instance len-cmatp (a (minor i j a)) (m (1- n)) (n (1- n))))
                  :in-theory (disable cmatp-minor len-cmatp))))

(defthm true-listp-minor
  (implies (and (acl2::cmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (true-listp (minor i j a)))
  :hints (("Goal" :use ((:instance cmatp-minor)
                        (:instance true-listp-cmatp (a (minor i j a)) (m (1- n)) (n (1- n))))
                  :in-theory (disable cmatp-minor true-listp-cmatp))))

(defthm len-minor0
  (implies (and (acl2::cmatp a n n) (natp n) (natp i) (< i n))
           (equal (len (acl2::minor0 a i)) (1- n)))
  :hints (("Goal" :in-theory (enable acl2::minor0))))

(defthm minor-i0-is-minor0
  (implies (and (acl2::cmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (minor i 0 a) (acl2::minor0 a i)))
  :hints (("Goal" :use ((:instance equal-from-all-nth-eq
                                   (x (minor i 0 a)) (y (acl2::minor0 a i)))
                        (:instance all-nth-eq-minors (k (1- n))))
                  :in-theory (disable all-nth-eq-minors))))

;; ---- the expansion of LDET, summed downward like Russinoff's
;; (LDET-PSUM a i n) = the first i terms of the expansion of an n x n matrix.
(defun ldet-psum (a i n)
  (if (zp i)
      0
    (+ (* (acl2::cof-sign (1- i)) (acl2::entry (1- i) 0 a)
          (acl2::ldet (acl2::minor0 a (1- i)) (1- n)))
       (ldet-psum a (1- i) n))))

(defthm ldet-sum-psum
  (implies (and (natp j) (natp n) (<= j n))
           (equal (+ (acl2::ldet-sum a j n (1- n)) (ldet-psum a j n))
                  (ldet-psum a n n)))
  :hints (("Goal" :induct (acl2::sum-ind j n))
          ("Subgoal *1/1" :expand ((acl2::ldet-sum a j n (1- n))
                                   (ldet-psum a (1+ j) n)))))

(defthm ldet-is-psum
  (implies (posp n)
           (equal (acl2::ldet a n) (ldet-psum a n n)))
  :hints (("Goal" :expand ((acl2::ldet a n))
                  :use ((:instance ldet-sum-psum (j 0))))))

;; ---- Russinoff's entry is ours
(defthm entry-same
  (equal (acl2::entry i j a) (entry i j a))
  :hints (("Goal" :in-theory (enable acl2::entry))))

;; ---- induction hypothesis: LDET and CDET agree on matrices of size m
(defun-sk ldet-cdet-p (m)
  (forall b (implies (acl2::cmatp b m m)
                     (equal (cdet b m) (acl2::ldet b m)))))

(defthm cexpand-col-aux-psum
  (implies (and (ldet-cdet-p (1- n))
                (acl2::cmatp a n n) (natp n) (> n 1)
                (natp i) (<= i n))
           (equal (cexpand-col-aux a i 0 n) (ldet-psum a i n)))
  :hints (("Goal" :induct (ldet-psum a i n)
                  :in-theory (disable ldet-cdet-p ldet-cdet-p-necc))
          ("Subgoal *1/2" :use ((:instance ldet-cdet-p-necc
                                           (m (1- n)) (b (minor (1- i) 0 a)))
                                (:instance cmatp-minor (i (1- i)) (j 0))
                                (:instance minor-i0-is-minor0 (i (1- i)))))))

;; ---- base cases
(defthm ldet-cdet-0
  (implies (acl2::cmatp b 0 0)
           (equal (cdet b 0) (acl2::ldet b 0)))
  :hints (("Goal" :in-theory (enable even-perm-p))))

(defthm cdet-1x1
  (implies (acl2::cmatp b 1 1)
           (equal (cdet b 1) (car (car b))))
  :hints (("Goal" :expand ((cdet b 1) (cdet-prod b '(0) 1) (cdet-prod b '(0) 0)
                           (acl2::cmatp b 1 1) (acl2::cmatp (cdr b) 0 1)
                           (acl2::clistnp (car b) 1) (acl2::clistnp (cdr (car b)) 0))
                  :in-theory (e/d (even-perm-p) (ldet-is-psum)))))

(defthm ldet-1x1
  (implies (acl2::cmatp b 1 1)
           (equal (acl2::ldet b 1) (car (car b))))
  :hints (("Goal" :expand ((acl2::ldet b 1) (acl2::ldet-sum b 0 1 0)
                           (acl2::ldet-sum b 1 1 0)
                           (acl2::ldet (acl2::minor0 b 0) 0)
                           (acl2::cof-sign 0)
                           (acl2::cmatp b 1 1) (acl2::cmatp (cdr b) 0 1)
                           (acl2::clistnp (car b) 1) (acl2::clistnp (cdr (car b)) 0))
                  :in-theory (e/d (acl2::entry) (ldet-is-psum)))))

(defthm ldet-cdet-1
  (implies (acl2::cmatp b 1 1)
           (equal (cdet b 1) (acl2::ldet b 1)))
  :hints (("Goal" :in-theory (disable ldet-is-psum))))

;; ---- the induction step
(defthm ldet-cdet-step
  (implies (and (ldet-cdet-p (1- n)) (natp n) (> n 1))
           (ldet-cdet-p n))
  :hints (("Goal" :do-not-induct t
                  :expand ((ldet-cdet-p n))
                  :in-theory (disable ldet-cdet-p ldet-cdet-p-necc
                                      cexpand-col-aux-psum cexpand-col-cdet
                                      ldet-is-psum)
                  :use ((:instance cexpand-col-aux-psum
                                   (a (ldet-cdet-p-witness n)) (i n))
                        (:instance cexpand-col-cdet
                                   (a (ldet-cdet-p-witness n)) (k 0))
                        (:instance ldet-is-psum
                                   (a (ldet-cdet-p-witness n)))))))

(defthm ldet-cdet-p-0
  (ldet-cdet-p 0)
  :hints (("Goal" :expand ((ldet-cdet-p 0))
                  :in-theory (disable ldet-cdet-p ldet-cdet-p-necc ldet-cdet-0)
                  :use ((:instance ldet-cdet-0 (b (ldet-cdet-p-witness 0)))))))

(defthm ldet-cdet-p-1
  (ldet-cdet-p 1)
  :hints (("Goal" :expand ((ldet-cdet-p 1))
                  :in-theory (disable ldet-cdet-p ldet-cdet-p-necc ldet-cdet-1)
                  :use ((:instance ldet-cdet-1 (b (ldet-cdet-p-witness 1)))))))

(defun dec-ind (n) (if (zp n) 0 (dec-ind (1- n))))

(defthm ldet-cdet-p-all
  (implies (natp n) (ldet-cdet-p n))
  :hints (("Goal" :induct (dec-ind n)
                  :in-theory (disable ldet-cdet-p ldet-cdet-p-necc ldet-cdet-step
                                      ldet-cdet-p-0 ldet-cdet-p-1))
          ("Subgoal *1/2" :cases ((equal n 1)))
          ("Subgoal *1/2.2" :use ((:instance ldet-cdet-step)))
          ("Subgoal *1/2.1" :use ((:instance ldet-cdet-p-1)))
          ("Subgoal *1/1" :use ((:instance ldet-cdet-p-0)))))

;; ======================= THEOREM: the bridge
;; The cofactor expansion LDET of poly-roots-traces is Leibniz's formula
;; (the sum over all permutations of signed products), in the form used by
;; Russinoff's books (CDET is his RDET instantiated to ACL2 numbers).
(defthm ldet-is-leibniz
  (implies (and (acl2::cmatp a n n) (natp n))
           (equal (acl2::ldet a n) (cdet a n)))
  :hints (("Goal" :use ((:instance ldet-cdet-p-necc (m n) (b a))
                        (:instance ldet-cdet-p-all))
                  :in-theory (disable ldet-cdet-p-necc ldet-cdet-p-all))))

;; ======================= the main theorems of poly-roots-traces, with Leibniz
;; The characteristic polynomial of an upper-triangular matrix, computed with
;; Leibniz's determinant (sum over all permutations of signed products).
(defthm char-poly-upper-tri-leibniz
  (implies (and (acl2::cmatp a n n) (acl2::c-upper-tri a n) (natp n)
                (acl2-numberp s))
           (equal (cdet (acl2::char-mat s a n) n)
                  (acl2::poly-eval (acl2::poly-from-roots (acl2::diag-list a 0 n)) s)))
  :hints (("Goal" :use ((:instance ldet-is-leibniz (a (acl2::char-mat s a n)))
                        (:instance acl2::cmatp-char-mat
                                   (acl2::s s) (acl2::a a) (acl2::n n))
                        (:instance acl2::char-poly-upper-tri
                                   (acl2::s s) (acl2::a a) (acl2::n n)))
                  :do-not-induct t
                  :in-theory (disable ldet-is-leibniz acl2::cmatp-char-mat
                                      acl2::char-poly-upper-tri cdet cdet-sum
                                      acl2::ldet acl2::char-mat))))

(defthm char-poly-from-traces-leibniz
  (implies (and (acl2::cmatp a n n) (posp n) (acl2::c-upper-tri a n)
                (acl2-numberp s) (natp k) (<= k n))
           (and (equal (cdet (acl2::char-mat s a n) n)
                       (acl2::poly-eval (acl2::poly-from-roots (acl2::diag-list a 0 n)) s))
                (equal (nth k (acl2::poly-from-roots (acl2::diag-list a 0 n)))
                       (* (expt -1 (- n k))
                          (car (acl2::e-from-traces (- n k) a n))))))
  :hints (("Goal" :use ((:instance char-poly-upper-tri-leibniz)
                        (:instance acl2::char-poly-from-traces
                                   (acl2::s s) (acl2::a a) (acl2::n n) (acl2::k k)))
                  :do-not-induct t
                  :in-theory (disable char-poly-upper-tri-leibniz
                                      acl2::char-poly-from-traces cdet cdet-sum
                                      acl2::char-mat))))
