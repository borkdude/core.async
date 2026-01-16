(ns cljs.core.async.impl.helpers
  (:require [cljs.core.async.impl.protocols :as impl]))

(defn fn-handler
  ([f] (fn-handler f true))
  ([f blockable]
   (reify
     impl/Handler
     (active? [_] true)
     (blockable? [_] blockable)
     (commit [_] f))))

(defn go-take! [ch]
  (let [resolve-fn (volatile! nil)]
    (if-some [ret (impl/take! ch (fn-handler (fn [v] (@resolve-fn v))))]
      @ret
      (js/Promise. (fn [resolve _]
                     (vreset! resolve-fn resolve))))))

(defn go-put! [ch val]
  (let [resolve-fn (volatile! nil)]
    (if-some [ret (impl/put! ch val (fn-handler (fn [v] (@resolve-fn v))))]
      @ret
      (js/Promise. (fn [resolve _]
                     (vreset! resolve-fn resolve))))))
