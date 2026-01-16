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

(defmethod analyze-sexpr 'do
  [[_ & body] env]
  (list* 'do (map #(analyze % env) body)))

(defmethod analyze-sexpr 'case
  [[_ val & body] env]
  (let [clauses (partition 2 body)
        default (when (odd? (count body))
                  (last body))]
    `(case ~(analyze val env)
       ~@(mapcat (fn [[clause body]]
                   [clause (analyze body env)])
                 clauses)
       ~@(when default [(analyze default env)]))))

;; ASYNC-221
(defmethod analyze-sexpr 'letfn*
  [[letfn* bindings & body] env]
  (let [locals (take-nth 2 bindings)
        assigned (take-nth 2 (rest bindings))
        env (update env :locals merge (zipmap locals locals))
        bindings (vec (interleave locals (map #(analyze % env) assigned)))
        body (map #(analyze % env) body)]
    (list* letfn* bindings body)))

(defmethod analyze-sexpr 'quote
  [expr env]
  expr)

(defmethod analyze-sexpr '.
  [[dot target method & args] env]
  (list* dot (analyze target env) method (map #(analyze % env) args)))

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

(defmethod analyze-sexpr 'try
  [[_ & body] env]
  (let [{:keys [body catches finally]} (destructure-try body)
        analyzed-body (map #(analyze % env) body)
        analyzed-catches (map (fn [[_ ex-type ex-sym & catch-body]]
                                (let [env' (assoc-in env [:locals ex-sym] ex-sym)
                                      catch-body (map #(analyze % env') catch-body)]
                                  `(catch ~ex-type ~ex-sym ~@catch-body)))
                              catches)
        analyzed-finally (when finally
                           (let [finally-body (map #(analyze % env) (rest finally))]
                             `(finally ~@finally-body)))]
    `(try
      ~@analyzed-body
      ~@analyzed-catches
      ~@(when analyzed-finally [analyzed-finally]))))

(defmethod analyze-sexpr 'fn*
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
                         (doall (list* args (map #(analyze % env) (rest x))))))]
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

(defmethod -analyze :list
  [lst env]
  (let [val (let [exp (expand env lst)
                  terminators (:terminators env)]
              (if (seq? exp)
                (if (symbol? (first exp))
                  (let [f (fixup-aliases (first exp) env)]
                    (cond
                      (is-special? f) (analyze-sexpr exp env)
                      (get (:locals env) f) (default-sexpr exp env)
                      (get terminators f) (terminate-custom (next exp) (get terminators f))
                      :else (default-sexpr exp env)))
                  (default-sexpr exp env))
                (analyze exp env)))]
    val))

(defmethod -analyze :default
  [x env] x)

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

(defn transform-awaits [env form]
  (-analyze form env))

(def async-custom-terminators
  {'<! 'cljs.core.async.impl.ioc-helpers/take!
   'cljs.core.async/<! 'cljs.core.async.impl.ioc-helpers/take!
   '>! 'cljs.core.async.impl.ioc-helpers/put!
   'cljs.core.async/>! 'cljs.core.async.impl.ioc-helpers/put!
   'alts! 'cljs.core.async/ioc-alts!
   'cljs.core.async/alts! 'cljs.core.async/ioc-alts!})
