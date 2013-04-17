#lang racket

; CESK state machine
;   control: a sequence of statements (stmts)
;   environment: frame pointer to this state machine (fp)
;   store: map of addr->values (store)
;   continuation: a seq of frames denoting procedure return contexts and
;                 exception handlers for this machine (kont)
(struct state {stmts fp stor kont})
(define empty (make-hash))

; lookup the value of the address
(define (lookup σ addr var)
    (hash-ref σ addr))

; extend store with a set of values
(define (extend σ addr val)
  (let ([val (cond [(set? val) val]
                   [(list? val) (list->set val)]
                   [else (set val)])])
        (hash-set σ addr (set-union (hash-ref σ addr (set)) val))))

; extend store with one or more values
(define (extend* σ fp vars vals)
  (let ([$fp (gensym fp)])
    (match `(,vars ,vals)
      [`((,var . ,vars) (,val . ,vals))
            (extend σ $fp var val)
            (extend* σ fp vars vals)]
      [else σ])))

; global label store
(define label-stor (make-hash))

; update the label store
(define (extend-label-stor label stmt)
  (hash-set! label-stor label stmt))

; lookup the statement from the label in the store
(define (lookup-label label)
  (hash-ref label-stor label))

; class struct
;   super -> a super classname or void
;   fields := store((op field) . value)
;   methods := hash(name . struct)
(struct class {super fields methods})
(struct method {formals body})

(define class-table (make-hash))

(define (extend-class-table name class)
  (hash-set! class-table name class))

(define (lookup/class name)
  (hash-ref class-table name))

; move up the class heir until you find a matching method
(define (lookup/method classname name)
  (let* ([class (lookup/class classname)]
         [methods (class-methods class)]
         [super (class-super class)])
    (if (hash-has-key? methods name)
        (hash-ref methods name)
        (if (void? (class-super class))
            (lookup/method (class-super class) name)
            (void)))))

; return true if base is a subclass of super
(define (isinstanceof super base)
    (if (void? super)
        #f  ; reached the top class
        (if (equal? super base)
            #t
            (let* ([class (lookup/class base)]
                   [upper (lookup/class super)])
              (if (equal? (class-super class) super)
                  #t
                  (isinstanceof (class-super upper) super))))))

; Apply continuation
(define (apply/κ κ val σ)
  (match κ
    ; assignment continuation
    [`(,name ,next-stmt ,fp ,κ_)
        (let ([σ_ (extend σ fp name val)])
          (state next-stmt fp σ_ κ_))]
    ; handle continuation
    [`(,classname ,label ,κ_) (apply/κ κ_ val σ)]
    ; the termination continuation
    ['halt (string-append "Answer: " (number->string val))]))

; method application
(define (apply/method m name val exps fp σ κ s)
  (let* ([fp_ (gensym fp)]
         [σ_ (extend σ fp_ "$this" val)]
         [κ_ `(,name ,s ,fp ,κ)])
    (let ([σ* (car (map (lambda (v e)
                     (extend σ_ fp_ v (eval/atomic e fp σ)))
                   (method-formals m) exps))])
      (state (method-body m) fp_ σ* κ_))))

; throw exception handler
(define (handle o fp σ ex)
  (match `(,o ,ex)
    [`((,op ,name) (,name_ ,l ,κ))  ; handler continuation
      (if (isinstanceof name_ name)
       `(,(lookup-label l) ,fp ,(extend σ fp "$ex" o) ,κ)
       (handle o fp σ κ))]  ; non-handler continuation
    [`(,val (,name ,s_ ,fp_ ,κ)) (handle val fp_ σ κ)]))


; AExp X FP X Store -> Value
(define (eval/atomic aexp ptr σ)
  (match aexp
    [(? atom?) aexp]
    [`(,v ,op ,n)
     (opify (eval/atomic v ptr σ) op (eval/atomic n ptr σ))]
    [else (lookup σ ptr aexp)]))

; get the set of atomic abstract values
(define (eval/atomic aexp ptr σ)
  (match aexp
    [(? atom?) (abstractify aexp)]
    [`(,v ,op ,n)
     (opify (eval/atomic v ptr σ) op (eval/atomic n ptr σ))]
    [else (lookup σ ptr (abstractify aexp))]))

; get abstract atomic values
(define (abstractify aexp)
  (match aexp
    [(? void?) 'NULL]
    [(? null?) 'NULL]
    [(? boolean?) 'BOOLEAN]
    [(? number?) 'NUMBER]))

; A helper to determine if these are plain values
(define (atom? aexp)
  (match aexp
    [(? void?) #t]
    [(? null?) #t]
    [(? boolean?) #t]
    [(? integer?) #t]
    [else #f]))

(define (opify lh op rh)
  (match op
    ['!= (not (= lh rh))]
    ['* (* lh rh)]
    ['- (- lh rh)]))

(define (next cur-state)
  ; extract the state struct's contents
  (if (state? cur-state)
      (let* ([stmts (state-stmts cur-state)]
             [fp (state-fp cur-state)]
             [σ (state-stor cur-state)]
             [κ (state-kont cur-state)]
             [current-stmt (first stmts)]
             [next-stmt (rest stmts)])
        (match current-stmt
          ; catch exceptions
          [`(move-exception ,e)
           (let ([$ex (lookup σ fp "$ex")])
             `(,next-stmt ,fp ,(extend σ fp $ex e)))]
          ; thrown exception
          [`(throw ,e) (handle (eval/atomic e fp σ) fp σ κ)]
          ; push and pop exception handlers
          [`(pushhandler ,name ,l)
           `(,next-stmt ,fp ,σ ,(cons `(,name ,l ,κ) κ))]
          [`(pophandler)
           `(,next-stmt ,fp ,σ ,(car κ))]
          ; return statement
          [`(return ,e) (apply/κ κ (eval/atomic e fp σ) σ)]
          ; assignment of method invocation
          [`(,name = invoke ,e ,mname ,vars)
           (let* ([$val (lookup σ fp e)]
                  [cname (match $val
                           [`(object ,cname ,fp) cname])]
                  [m (lookup/method cname mname)])
             (apply/method m name $val vars fp σ κ next-stmt))]
          ; new object creation/assignment
          [`(,varname = new ,classname)
           (let* ([op_ `(object ,classname ,(gensym))]
                  [σ_ (extend σ fp varname op_)])
             (state next-stmt fp σ_ κ))]
          ; assignment aexp
          [`(,varname = ,aexp)
           (let* ([val (eval/atomic aexp fp σ)]
                  [σ_ (extend σ fp varname val)])
             (state next-stmt fp σ_ κ))]
          ; label stmt
          [`(label ,l)
           (state next-stmt fp σ κ)]
          ; if-goto stmt
          [`(if ,e goto ,l)
           ;=>
           (if (eval/atomic e fp σ)
               (state (lookup-label l) fp σ κ)
               (state next-stmt fp σ κ))]
          ; goto stmt
          [`(goto ,l) (state (lookup-label l) fp σ κ)]
          ; skip stmt
          ['(nop) (state next-stmt fp σ κ)]))
      cur-state))

(define (parse-program program)
  (match program
    [`(program . ,exps) (map eval-program-exps exps)]
    [else (error "Not a program ~s" program)]))

(define (eval-program-exps exps)
  (match exps
    [`(class ,name . ,defs)
        ; =>
        (let ([fields '()]
              [methods (make-hash)])
          (map (lambda (d) (eval-def d fields methods)) defs)
          (extend-class-table name (class void fields methods)))]
    [`(class ,name extends ,super ,defs)
        ; =>
        (let ([fields '()]
              [methods (make-hash)])
          (map (lambda (d) (eval-def d fields methods)) defs)
          (extend-class-table name (class super fields methods)))]
    [else (error "No program exps ~s" exps)]))

(define (eval-def def fields methods)
  (match def
    [`(def ,name ,args ,body)
        (eval-meth-body body)
        (hash-set! methods name (method args body))]
    [`(var ,name) (cons `(,name ,void) fields)]))

(define (eval-meth-body body)
    (match body
      [`() '()]
      [`((label ,l) . ,rest) (extend-label-stor l rest) (eval-meth-body rest)]
      [`(,blah . ,rest) (eval-meth-body rest)]))

(define empty-fp (gensym))

(define (inject stmt)
  (state stmt empty-fp (make-immutable-hash) 'halt))

(define (run state)
  (if (state? state)
      (let ([step (next state)])
        (run step))
      (printf "~s\n" state)))


(define factorialprog
  '(program
    (class F
        (def fact(n)((if (n != 1) goto next)
                     (return n)
                     (label next)
                     (n1 = (n - 1))
                     (n2 = invoke "$this" fact(n1))
                     (ret = (n * n2))
                     (return ret))))))
(define factorialstmt
    '((f = new F)
      (i = invoke f fact (5))
      (return i)))

(define run-fact
  (begin
    (parse-program factorialprog)
    (let ([s0 (inject factorialstmt)])
      (run s0))))

; vim: tabstop=2 shiftwidth=2 softtabstop=2
