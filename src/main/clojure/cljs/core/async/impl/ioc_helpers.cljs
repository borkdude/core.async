;;   Copyright (c) Rich Hickey and contributors. All rights reserved.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns cljs.core.async.impl.ioc-helpers
  (:require [cljs.core.async.impl.protocols :as impl]))

(defn- fn-handler
  [f]
  (reify
   impl/Handler
   (active? [_] true)
   (blockable? [_] true)
   (commit [_] f)))

(defn take! [ch]
  (let [resolve-fn (volatile! nil)]
    (if-some [ret (impl/take! ch (fn-handler (fn [v] (@resolve-fn v))))]
      @ret
      (js/Promise. (fn [resolve _]
                     (vreset! resolve-fn resolve))))))

(defn put! [ch val]
  (let [resolve-fn (volatile! nil)]
    (if-some [ret (impl/put! ch val (fn-handler (fn [v] (@resolve-fn v))))]
      @ret
      (js/Promise. (fn [resolve _]
                     (vreset! resolve-fn resolve))))))
