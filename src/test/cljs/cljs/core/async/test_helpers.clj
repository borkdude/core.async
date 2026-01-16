;;   Copyright (c) Rich Hickey and contributors. All rights reserved.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns cljs.core.async.test-helpers)

(defmacro assert-go-block-completes
  [nm & body]
  `(let [body-chan# (do ~@body)
         timeout# (fn [] (let [c# (cljs.core.async/chan)]
                           (cljs.core.async.macros/go
                             (cljs.core.async/<! (cljs.core.async/timeout 10000))
                             (cljs.core.async/>! c# ::timeout)
                             (cljs.core.async/close! c#))
                           c#))]
     (when (satisfies? cljs.core.async.impl.protocols.Channel body-chan#)
       (cljs.core.async.macros/go
         (let [[v# c#] (cljs.core.async/alts! [body-chan# (timeout#)] :priority true)]
           (assert (not= ::timeout v#)
                   (str "test timed out: " ~nm ))))
       true)))

(defmacro deftest
  [nm & body]
  `(do (.log js/console (str "Testing: " ~(str nm) "..."))
       (assert-go-block-completes ~(str nm) ~@body)))

(defmacro throws?
  [& exprs]
  `(try ~@exprs false
        (catch ~'js/Object e# true)))

(defmacro testing
  [nm & body]
    `(do (.log js/console (str "    " ~nm "..."))
         (assert-go-block-completes ~(str nm) ~@body)))

(defmacro is=
  [a b]
  `(let [a# ~a
         b# ~b]
     (assert (= a# b#) (str a# " != " b#))))

(defmacro is
  [a]
  `(assert ~a))

(defmacro locals-test []
  (if (get-in &env [:locals] 'x)
    :pass
    :fail))
