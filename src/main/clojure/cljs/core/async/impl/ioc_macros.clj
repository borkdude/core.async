;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

;; by Timothy Baldridge
;; April 13, 2013

;; rewritten to JS async/await by Michiel Borkent
;; January 2026

(ns cljs.core.async.impl.ioc-macros
  (:require [cljs.analyzer :as cljs]
            [clojure.pprint :refer [pprint]])
  (:import [cljs.tagged_literals JSValue]))

(defn debug [x]
  (binding [*out* *err*]
    (pprint x))
  x)

;; Dispatch clojure forms based on data type
(defmulti transform (fn [x _env]
                       (cond
                         (symbol? x) :symbol
                         (seq? x) :list
                         (map? x) :map
                         (set? x) :set
                         (vector? x) :vector
                         (instance? JSValue x) :js-value
                         :else :default)))

;; Given an sexpr, dispatch on the first item
(defmulti transform-special
  (fn [x env]
    (first x)))

;; NOTE: we only need to handle special forms that either introduce locals (e.g
;; `let*`, `try`) or have special parts that are treated like quoted
;; values (`case`). Special forms like `if`, `recur` etc. do not need special
;; handling.

(defn special? [x]
  (let [^clojure.lang.MultiFn mfn transform-special]
    (.getMethod mfn x)))

(defn transform-seq [args env]
  (map #(transform % env) args))

(defmethod transform-special 'let*
  [[_ binds & body] env]
  (let [parted (partition 2 binds)
        [env binds] (reduce (fn [[env binds] [k v]]
                                 (let [env (assoc-in env [:locals k] k)]
                                   [env (conj binds k (transform v env))] ))
                               [env []]
                               parted)]
    `(let* ~binds ~(transform `(do ~@body) env))))

(defmethod transform-special 'loop*
  [[_ binds & body] env]
  (let [parted (partition 2 binds)
        [env binds] (reduce (fn [[env binds] [k v]]
                              (let [env (assoc-in env [:locals k] k)]
                                [env (conj binds k (transform v env))] ))
                            [env []]
                            parted)]
    `(loop* ~binds ~(transform `(do ~@body) env))))

(defmethod transform-special 'case
  [[_ val & body] env]
  (let [clauses (partition 2 body)
        default (when (odd? (count body))
                  (last body))]
    `(case ~(transform val env)
       ~@(mapcat (fn [[clause body]]
                   [clause (transform body env)])
                 clauses)
       ~@(when default [(transform default env)]))))

;; ASYNC-221
(defmethod transform-special 'letfn*
  [[letfn* bindings & body] env]
  (let [locals (take-nth 2 bindings)
        assigned (take-nth 2 (rest bindings))
        env (update env :locals merge (zipmap locals locals))
        bindings (vec (interleave locals (map #(transform % env) assigned)))
        body (map #(transform % env) body)]
    (list* letfn* bindings body)))

(defmethod transform-special 'quote
  [expr env]
  expr)

(defn destructure-try
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

(defmethod transform-special 'try
  [[_ & body] env]
  (let [{:keys [body catches finally]} (destructure-try body)
        transformed-body (map #(transform % env) body)
        transformed-catches (map (fn [[_ ex-type ex-sym & catch-body]]
                                   (let [env' (assoc-in env [:locals ex-sym] ex-sym)
                                         catch-body (map #(transform % env') catch-body)]
                                     `(catch ~ex-type ~ex-sym ~@catch-body)))
                                 catches)
        transformed-finally (when finally
                              (let [finally-body (map #(transform % env) (rest finally))]
                                `(finally ~@finally-body)))]
    `(try
      ~@transformed-body
      ~@transformed-catches
      ~@(when transformed-finally [transformed-finally]))))

(defmethod transform-special 'fn*
  [fn-expr env]
  (let [prelude (take-while (complement sequential?) fn-expr)
        nm (second prelude)
        env (if nm (assoc-in env [:locals nm] nm) env)
        remainder (drop (count prelude) fn-expr)
        remainder (if (vector? (first remainder))
                    (list remainder) remainder)
        body-handler (fn [env x]
                       (let [args (first x)
                             locals (zipmap args args)
                             env (update env :locals merge locals)]
                         (list* args (map #(transform % env) (rest x)))))]
    (concat prelude (map #(body-handler env %) remainder))))

(def special-override? '#{case clojure.core/case
                          try clojure.core/try})

(defn expand [env form]
  (let [locals (:locals env)]
    (loop [form form]
      (if-not (seq? form)
        form
        (let [[s & r] form]
          (if (symbol? s)
            (if (or (get locals s)
                    (special-override? s))
              form
              (let [new-env (update env :locals merge locals)
                    expanded (cljs/macroexpand-1 new-env form)]
                (if (= expanded form)
                  form
                  (recur expanded))))
            form))))))

(defn fixup-aliases [sym env]
  (let [aliases (ns-aliases *ns*)]
    (if-not (namespace sym)
      sym
      (if-let [ns (or (get-in env [:ns :requires-macros (symbol (namespace sym))])
                      (get-in env [:ns :requires (symbol (namespace sym))]))]
        (symbol (name ns) (name sym))
        sym))))

(defn terminate-custom [args op]
  `(let [v# ~(list* op args)]
     (if (instance? js/Promise v#)
       (cljs.core/await v#)
       v#)))

(defmethod transform :list
  [lst env]
  (let [val (let [exp (expand env lst)
                  terminators (:terminators env)
                  first-expr (first exp)]
              (if (seq? exp)
                (if (symbol? first-expr)
                  (let [f (fixup-aliases first-expr env)]
                    (cond
                      (special? f) (transform-special exp env)
                      (get (:locals env) f) (transform-seq exp env)
                      (get terminators f) (terminate-custom (next exp) (get terminators f))
                      :else (transform-seq exp env)))
                  (transform-seq exp env))
                (transform exp env)))]
    val))

(defmethod transform :default
  [x env] x)

(defmethod transform :symbol
  [x env] x)

(defmethod transform :map
  [x env]
  (transform `(hash-map ~@(mapcat identity x)) env))

(defmethod transform :vector
  [x env]
  (transform `(vector ~@x) env))

(defmethod transform :js-value
  [^JSValue x env]
  (let [items (.-val x)]
    (if (map? items)
      (transform `(cljs.core/js-obj ~@(mapcat (fn [[k v]] [(name k) v]) items)) env)
      (transform `(cljs.core/array ~@items) env))))

(defmethod transform :set
  [x env]
  (transform `(hash-set ~@x) env))

(defn transform-body [body env user-transitions]
  (transform (if (= 1 (count body))
               (first body)
               (list* 'do body))
             (assoc env :terminators user-transitions)))

(def async-custom-terminators
  {'<! 'cljs.core.async.impl.ioc-helpers/take!
   'cljs.core.async/<! 'cljs.core.async.impl.ioc-helpers/take!
   '>! 'cljs.core.async.impl.ioc-helpers/put!
   'cljs.core.async/>! 'cljs.core.async.impl.ioc-helpers/put!
   'alts! 'cljs.core.async/ioc-alts!
   'cljs.core.async/alts! 'cljs.core.async/ioc-alts!})
