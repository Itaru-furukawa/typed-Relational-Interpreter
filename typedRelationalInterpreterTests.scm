(load "alphaKanren.scm")

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (printf "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                     'tested-expression expected produced)))))))

(test "1"
 (run 1 (q)
      (fresh (x)
             (exist (val t-val)
                    (t-eval-expo `(lambda ,(tie x x)) '() val '() t-val)
                    (== q `(,val ,t-val)))))
 '(((closure (tie-tag a.0 a.0) ()) (_.0 -> _.0))))

(test "2"
 (run 1 (q)
      (fresh (x y)
             (exist (val t-val)
                    (t-eval-expo `(lambda ,(tie x `(lambda ,(tie y x)))) '() val '() t-val)
                    (== q `(,val ,t-val)))))
 '(((closure (tie-tag a.0 (lambda (tie-tag a.1 a.0))) ()) (_.0 -> (_.1 -> _.0)))))

(test "3"
 (run 1 (q)
      (fresh (x y)
             (exist (val t-val)
                    (t-eval-expo `(lambda ,(tie x `(lambda ,(tie y x)))) '() val '() t-val)
                    (== q `(,val ,t-val)))))
 '(((closure (tie-tag a.0 (lambda (tie-tag a.1 a.0))) ()) (_.0 -> (_.1 -> _.0)))))

(test "4"
 (fmt (run 1 (q)
       (fresh (let-var1 let-var2 a b)
              (exist (blank val t-val exp1 exp2 exp3 exp2^ exp3^ x1 y1 x2 y2 exp2-body exp3-body)
                     (== exp1 `(let (,let-var2 . (,let-var1 #t)) ,(tie let-var2 `(if ,let-var2 ,blank (,let-var1 (int-exp 7))))))
                     (== exp2 `(let (,let-var1 . (lambda ,(tie a a))) ,(tie let-var1 exp1)))
                     (t-eval-expo exp2 '() val '() t-val)
                     (== q `(,blank ,val ,t-val))))))
 '(((int-exp _.0) _.0 int)))
