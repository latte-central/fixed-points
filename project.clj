(defproject fixed-points "0.0.3"
  :description "A bit of fixed point theory (in LaTTe)."
  :url "https://github.com/fredokun/fixed-points.git"
  :license {:name "Creative Commons CC-BY-SA 4.0"
            :url "https://creativecommons.org/licenses/by-sa/4.0/"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [latte "0.3.1-SNAPSHOT"]
                 [latte-sets "0.0.5-SNAPSHOT"]]
  :codox {:metadata {:doc/format :markdown}
          :namespaces [latte-sets.core]}
  :plugins [[lein-gorilla "0.3.6"]])


