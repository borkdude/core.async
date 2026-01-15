;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

;; by Timothy Baldridge
;; April 13, 2013

(ns cljs.core.async.impl.ioc-macros
  (:refer-clojure :exclude [all])
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :refer (intersection)]
            [cljs.analyzer :as cljs]
            [clojure.walk :as walk])
  (:import [cljs.tagged_literals JSValue]))

(defn debug [x]
  (binding [*out* *err*]
    (pprint x))
  x)

;; Dispatch clojure forms based on data type
(defmulti -analyze (fn [x _env]
                     (cond
                       (symbol? x) :symbol
                       (seq? x) :list
                       (map? x) :map
                       (set? x) :set
                       (vector? x) :vector
                       (instance? JSValue x) :js-value
                       :else :default)))

(defn analyze [x env]
  (-analyze x env))

;; given an sexpr, dispatch on the first item
(defmulti analyze-sexpr (fn [x env]
                     (first x)))

(defn is-special? [x]
  (let [^clojure.lang.MultiFn mfn analyze-sexpr]
    (.getMethod mfn x)))

(defn default-sexpr [args env]
  (map #(analyze % env) args))

(defmethod analyze-sexpr 'let*
  [[_ binds & body] env]
  (let [parted (partition 2 binds)
        [env binds] (reduce (fn [[env binds] [k v]]
                                 (let [env (assoc-in env [:locals k] k)]
                                   [env (conj binds k (analyze v env))] ))
                               [env []]
                               parted)]
    `(let* ~binds ~(analyze `(do ~@body) env))))

(defmethod analyze-sexpr 'loop*
  [[_ binds & body] env]
  (let [parted (partition 2 binds)
        [env binds] (reduce (fn [[env binds] [k v]]
                              (let [env (assoc-in env [:locals k] k)]
                                [env (conj binds k (analyze v env))] ))
                            [env []]
                            parted)]
    `(loop* ~binds ~(analyze `(do ~@body) env))))

#_(defmethod analyze* 'set!
  [[_ assignee val]]
  (let [target (cond
                 (symbol? assignee)
                 assignee
                 (and (list? assignee)
                      (= (count assignee) 2))
                 (second assignee))
        field (if (list? assignee)
                (first assignee))]
    (gen-plan
     [locals (get-binding :locals)

      target-id (if (contains? locals target)
                  (fn [p]
                    [(get locals target) p])
                  (item-to-ssa target))
      val-id    (item-to-ssa val)

      ret-id (add-instruction (->Set! field target-id val-id))]
     ret-id)))

(defmethod analyze-sexpr 'do
  [[_ & body] env]
  (debug :body) (debug body)
  (list* 'do (map #(analyze % env) body)))

#_(defmethod analyze* 'case
  [[_ val & body]]
  (let [clauses (partition 2 body)
        default (when (odd? (count body))
                  (last body))]
    (gen-plan
     [end-blk (add-block)
      start-blk (get-block)
      clause-blocks (all (map (fn [expr]
                                (gen-plan
                                 [blk-id (add-block)
                                  _ (set-block blk-id)
                                  expr-id (item-to-ssa expr)
                                  _ (if (not= expr-id ::terminated)
                                      (add-instruction (->Jmp expr-id end-blk))
                                      (no-op))]
                                 blk-id))
                              (map second clauses)))
      default-block (if (odd? (count body))
                      (gen-plan
                       [blk-id (add-block)
                        _ (set-block blk-id)
                        expr-id (item-to-ssa default)
                        _ (if (not= expr-id ::terminated)
                            (add-instruction (->Jmp expr-id end-blk))
                            (no-op))]
                       blk-id)
                      (no-op))
      _ (set-block start-blk)
      val-id (item-to-ssa val)
      case-id (add-instruction (->Case val-id (map first clauses) clause-blocks default-block))
      _ (set-block end-blk)
      ret-id (add-instruction (->Const ::value))]
     ret-id)))

(defmethod analyze-sexpr 'quote
  [expr]
  expr)

(defmethod analyze-sexpr '.
  [[_ target method & args] env]
  #_(let [args (if (seq? method)
               (next method)
               args)
        method (if (seq? method)
                 (first method)
                 method)]
    #_(gen-plan
     [target-id (item-to-ssa target)
      args-ids (all (map item-to-ssa args))
      ret-id (add-instruction (->Dot target-id method args-ids))]
     ret-id)))

#_(defn destructure-try
  [body]
  (reduce
   (fn [accum form]
     (case (:state accum)
       :body (cond
              (and (seq? form) (= (first form) 'catch)) (-> accum
                                                            (assoc :state :catch)
                                                            (update-in [:catches] conj form))
              (and (seq? form) (= (first form) 'finally)) (-> accum
                                                              (assoc :state :finally)
                                                              (assoc :finally form))
              :else (update-in accum [:body] conj form))
       :catch (cond
               (and (seq? form) (= (first form) 'catch)) (-> accum
                                                             (assoc :state :catch)
                                                             (update-in [:catches] conj form))
               (and (seq? form) (= (first form) 'finally)) (-> accum
                                                               (assoc :state :finally)
                                                               (assoc :finally form))
               :else (throw (Exception. "Only catch or finally clause can follow catch in try expression")))
       :finally (throw (Exception. "finally clause must be last in try expression"))))
   {:state :body
    :body []
    :catches []
    :finally nil}
   body))

#_(defmethod analyze* 'try
  [[_ & body]]
  (let [{:keys [body catches finally] :as m} (destructure-try body)]
    (gen-plan
     [body-block (add-block)
      exit-block (add-block)
      finally-blk (if finally
                    (gen-plan
                     [cur-blk (get-block)
                      finally-blk (add-block)
                      _ (set-block finally-blk)
                      _ (add-instruction (->PopTry))
                      result-id (add-instruction (->Const ::value))
                      _ (item-to-ssa (cons 'do (rest finally)))
                      ;; rethrow exception on exception path
                      _ (add-instruction (->EndFinally))
                      _ (add-instruction (->Jmp result-id exit-block))
                      _ (set-block cur-blk)]
                     finally-blk)
                    (gen-plan [] exit-block))
      catch-blocks (all
                    (for [[_ ex ex-bind & catch-body] catches]
                      (gen-plan
                       [cur-blk (get-block)
                        catch-blk (add-block)
                        _ (set-block catch-blk)
                        ex-id (add-instruction (->Const ::value))
                        ;; TODO: type hint ex-bind?
                        _ (push-alter-binding :locals assoc ex-bind ex-id)
                        result-id (item-to-ssa (cons 'do catch-body))
                        ;; if there is a finally, jump to it after
                        ;; handling the exception, if not jump to exit
                        _ (add-instruction (->Jmp result-id finally-blk))
                        _ (pop-binding :locals)
                        _ (set-block cur-blk)]
                       [catch-blk ex])))
      catch-handler-block (add-block)
      cur-blk (get-block)
      _ (set-block catch-handler-block)
      _ (add-instruction (->PopTry))
      _ (add-instruction (->CatchHandler catch-blocks))
      _ (set-block cur-blk)
      _ (add-instruction (->Jmp nil body-block))
      _ (set-block body-block)
      ;; the finally gets pushed on to the exception handler stack, so
      ;; it will be executed if there is an exception
      _ (if finally
          (add-instruction (->PushTry finally-blk))
          (no-op))
      _ (add-instruction (->PushTry catch-handler-block))
      body (item-to-ssa (cons 'do body))
      _ (add-instruction (->PopTry))
      ;; if the body finishes executing normally, jump to the finally
      ;; block, if it exists
      _ (add-instruction (->Jmp body finally-blk))
      _ (set-block exit-block)
      ret (add-instruction (->Const ::value))]
     ret)))

#_(defmethod analyze* 'recur
  [[_ & vals]]
  (gen-plan
   [val-ids (all (map item-to-ssa vals))
    recurs (get-binding :recur-nodes)
    _ (do (assert (= (count val-ids)
                     (count recurs))
                  "Wrong number of arguments to recur")
          (no-op))
    _ (add-instruction (->Recur recurs val-ids))

    recur-point (get-binding :recur-point)
    _ (add-instruction (->Jmp nil recur-point))]
   ::terminated))

#_(defmethod analyze* 'if
  [[_ test then else]]
  (gen-plan
   [test-id (item-to-ssa test)
    then-blk (add-block)
    else-blk (add-block)
    final-blk (add-block)
    _ (add-instruction (->CondBr test-id then-blk else-blk))

    _ (set-block then-blk)
    then-id (item-to-ssa then)
    _ (if (not= then-id ::terminated)
        (gen-plan
         [_ (add-instruction (->Jmp then-id final-blk))]
         then-id)
        (no-op))

    _ (set-block else-blk)
    else-id (item-to-ssa else)
    _ (if (not= else-id ::terminated)
        (gen-plan
         [_ (add-instruction (->Jmp else-id final-blk))]
         then-id)
        (no-op))

    _ (set-block final-blk)
    val-id (add-instruction (->Const ::value))]
   val-id))

#_(defmethod analyze* 'fn*
  [& fn-expr]
  ;; For fn expressions we just want to record the expression as well
  ;; as a list of all known renamed locals
  (gen-plan
   [locals (get-binding :locals)
    fn-id (add-instruction (->Fn fn-expr (keys locals) (vals locals)))]
   fn-id))


(def special-override? '#{case clojure.core/case
                          try clojure.core/try})

(defn expand [locals env form]
  (loop [form form]
    (if-not (seq? form)
      form
      (let [[s & r] form]
        (if (symbol? s)
          (if (or (get locals s)
                  (special-override? s))
            form
            (let [new-env (update-in env [:locals] merge locals)
                  expanded (cljs/macroexpand-1 new-env form)]
              (if (= expanded form)
                form
                (recur expanded))))
          form)))))

(defn fixup-aliases [sym env]
  (let [aliases (ns-aliases *ns*)]
    (if-not (namespace sym)
      sym
      (if-let [ns (or (get-in env [:ns :requires-macros (symbol (namespace sym))])
                      (get-in env [:ns :requires (symbol (namespace sym))]))]
        (symbol (name ns) (name sym))
        sym))))

(defmethod -analyze :list
  [lst env]
  (let [locals (:locals env)
        val (let [exp (expand locals env lst)]
              (if (seq? exp)
                (if (symbol? (first exp))
                  (let [f (fixup-aliases (first exp) env)]
                    (cond
                      (is-special? f) (analyze-sexpr exp env)
                      (get locals f) (default-sexpr exp env)
                      #_#_(get terminators f) (terminate-custom (next exp) (get terminators f))
                      :else (default-sexpr exp env)))
                  (default-sexpr exp env))
                (analyze exp env)))]
    val))

(defmethod -analyze :default
  [x env]
  (debug :default)
  (debug x)
  x)

(defmethod -analyze :symbol
  [x env] x)

(defmethod -analyze :map
  [x env]
  (-analyze `(hash-map ~@(mapcat identity x)) env))

(defmethod -analyze :vector
  [x env]
  (-analyze `(vector ~@x) env))

(defmethod -analyze :js-value
  [^JSValue x env]
  (let [items (.-val x)]
    (if (map? items)
      (-analyze `(cljs.core/js-obj ~@(mapcat (fn [[k v]] [(name k) v]) items)) env)
      (-analyze `(cljs.core/array ~@items) env))))

(defmethod -analyze :set
  [x env]
  (-analyze `(hash-set ~@x) env))

(defn strip-core-ns [sym]
  (when (symbol? sym)
    (if-let [ns (namespace sym)]
      (when (= "cljs.core.async" ns)
        (symbol (name sym)))
      sym)))

(defn transform-awaits [env form]
  (let [res (-analyze form env)]
    (debug :res)
    (debug res)
    res)
  #_(let [locals (:locals env)
        form* form
        form (expand locals env form)]
    (binding [*out* *err*] (prn :expanded form))
    (walk/postwalk
     (fn [x]
       (cond
         (and (seq? x) (= '<! (strip-core-ns (first x))))
         `(cljs.core/await (cljs.core.async/take-promise ~(second x)))
         (and (seq? x) (= '>! (strip-core-ns (first x))))
         `(cljs.core/await (cljs.core.async/put-promise ~(second x) ~(nth x 2)))
         (and (seq? x) (= 'alts! (strip-core-ns (first x))))
         `(cljs.core/await (cljs.core.async/alts-promise ~@(rest x)))
         :else x))
     form)))

(def async-custom-terminators
  {'<! 'cljs.core.async.impl.ioc-helpers/take!
   'cljs.core.async/<! 'cljs.core.async.impl.ioc-helpers/take!
   '>! 'cljs.core.async.impl.ioc-helpers/put!
   'cljs.core.async/>! 'cljs.core.async.impl.ioc-helpers/put!
   'alts! 'cljs.core.async/ioc-alts!
   'cljs.core.async/alts! 'cljs.core.async/ioc-alts!
   :Return 'cljs.core.async.impl.ioc-helpers/return-chan})

#_(defn state-machine [body num-user-params env user-transitions]
  (-> (parse-to-state-machine body env user-transitions)
      second
      (emit-state-machine num-user-params user-transitions)))
