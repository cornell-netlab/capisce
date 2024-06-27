(declare-const _symb$get_type$action$_$0 (_ BitVec 1))
(declare-const _symb$get_type$match_0$_$0 (_ BitVec 16))
(declare-const _symb$get_type$packet_type$arg$version$_$0 (_ BitVec 1))
(declare-const _symb$ipv4_encap$action$_$0 (_ BitVec 1))
(declare-const _symb$ipv4_encap$match_0$_$0 (_ BitVec 16))
(declare-const _symb$ipv6_encap$action$_$0 (_ BitVec 1))
(declare-const _symb$ipv6_encap$match_0$_$0 (_ BitVec 16))

;; (assert
;;  (not
;;   (=
(assert (not (=
              ;; (not (and (= _symb$ipv6_encap$match_0$_$0 _symb$ipv4_encap$match_0$_$0)
              ;;           (or (= _symb$ipv4_encap$match_0$_$0 #x0800)
              ;;               (= _symb$ipv4_encap$match_0$_$0 #x86dd))))

              (=> (or (= _symb$ipv4_encap$match_0$_$0 #x0800)
                      (= _symb$ipv4_encap$match_0$_$0 #x86dd))
                  (not (= _symb$ipv6_encap$match_0$_$0 _symb$ipv4_encap$match_0$_$0)))

              (let ((a!1 (or (not (= _symb$ipv4_encap$action$_$0 #b0))
                             (and (not (= _symb$ipv6_encap$action$_$0 #b0))
                                  (not (= _symb$ipv6_encap$action$_$0 #b1)))))
                    (a!2 (or (and (not (= _symb$ipv4_encap$action$_$0 #b0))
                                  (not (= _symb$ipv4_encap$action$_$0 #b1)))
                             (and (not (= _symb$ipv6_encap$action$_$0 #b0))
                                  (not (= _symb$ipv6_encap$action$_$0 #b1)))))
                    (a!3 (not (and (not (= _symb$ipv6_encap$action$_$0 #b0))
                                   (not (= _symb$ipv6_encap$action$_$0 #b1)))))
                    (a!4 (not (and (not (= _symb$ipv4_encap$action$_$0 #b0))
                                   (not (= _symb$ipv4_encap$action$_$0 #b1))))))
                (let ((a!5 (or (and (or (= _symb$ipv4_encap$match_0$_$0 #x0800)
                                        (= _symb$ipv4_encap$match_0$_$0 #x86dd))
                                    (not (and a!1 a!2)))
                               (and (= _symb$ipv4_encap$match_0$_$0 #x0800) (not (and a!1 a!2)))
                               (and a!3 a!4 (= _symb$ipv4_encap$match_0$_$0 #x86dd)))))
                  (not (and (= _symb$ipv6_encap$match_0$_$0 _symb$ipv4_encap$match_0$_$0) a!5)))))))



(check-sat)
