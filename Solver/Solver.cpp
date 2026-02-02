/**
* @author Tim Luchterhand
* @date 27.11.24
* @brief
*/

#include "Solver.hpp"
#include "util/exception.hpp"


namespace sat {
    

    Solver::Solver(unsigned numVariables) {
        this->numVariables = numVariables;
        this->clauses = std::vector<ClausePointer>();

        this->model = std::unordered_map<unsigned, TruthValue>();
        for (unsigned i = 0; i <= numVariables; ++i){
            model[i] = TruthValue::Undefined;
        }

        this->unitLiterals = std::vector<Literal>();
        this->watches = LitMap();

    }

    bool Solver::addClause(Clause clause) {
        if (clause.size() < 1){
            return false;
        } else if (clause.size() == 1){
            Literal l = clause[0];

            if (falsified(l)){
                return false;
            } else {
                this->assign(l);
                return true;
            }
        }else{
            ClausePointer clausePtr = std::make_shared<Clause>(clause);
            clauses.push_back(clausePtr);

            Literal firstWatcher = clause.getWatcherByRank(0);
            Literal secondWatcher = clause.getWatcherByRank(1);

            if (firstWatcher != NULL) {
                watches[firstWatcher.get()].push_back(clauses.back());
            }

            if (secondWatcher != NULL) {
                watches[secondWatcher.get()].push_back(clauses.back());
            }

            return true;
        }
    }

    /**
     * Here you have a possible implementation of the rebase-method. It should work out of the box.
     * To use it, remove the throw-expression and un-comment the code below. The implementation requires that
     * your solver has some sort of container of pointer types to clause called 'clauses'
     * (e.g. std::vector<ClausePointer>). Additionally, your solver needs to have a container of unit literals
     * called 'unitLiterals'.
     */
    auto Solver::rebase() const -> std::vector<Clause> {
        std::vector<Clause> reducedClauses;
        // We check all clauses in the solver. If the clause is SAT (at least one literal is satisfied), we don't include it.
        // Additionally, we remove all falsified literals from the clauses since we only care about unassigned literals.
        for (const auto &c: clauses) {
            bool sat = false;
            // We're creating a new (possibly smaller clause from the current clause c)
            std::vector<Literal> newLits;
            newLits.reserve(c->size());
            // For each literal l in the clause we check if l is satisfied or falsified
            for (auto l: *c) {
                if (satisfied(l)) {
                    // in this case, the whole clause is satisfied and can be removed entirely from the solver
                    sat = true;
                    break;
                }

                if (!falsified(l)) {
                    // only unassigned literals are added to the reduced clause
                    newLits.emplace_back(l);
                }
            }

            if (!sat) {
                // create the new clause (move all the literals inside the Clause-class)
                Clause newClause(std::move(newLits));
                // Check if we already added an equivalent clause
                auto res = std::ranges::find_if(reducedClauses, [&newClause](const auto &clause) {
                    return clause.sameLiterals(newClause);
                });
                if (res == reducedClauses.end()) {
                    // The new clause is not yet contained => add it
                    reducedClauses.emplace_back(std::move(newClause));
                }
            }
        }

        // Finally, we need to add all the unit literals as well
        for (Literal l: unitLiterals) {
            reducedClauses.emplace_back(std::vector{l});
        }

        return reducedClauses;
    }

    TruthValue Solver::val(Variable x) const {
        if(model.find(x.get()) != model.end()) {
            return model.at(x.get());
        }
        else{
            return TruthValue::Undefined;
        }
    }

    bool Solver::satisfied(Literal l) const {
        Variable var = sat::var(l);
        if(model.find(var.get()) != model.end()) {
            return model.at(var.get()) == (l.sign() == 1 ? TruthValue::True : TruthValue::False);
        }else{
            return false;
        }
    }

    bool Solver::falsified(Literal l) const {
        Variable var = sat::var(l);
        if(model.find(var.get()) != model.end()) {
            return model.at(var.get()) == (l.sign() == 1 ? TruthValue::False : TruthValue::True);
        }else{
            return false;
        }
    }


    bool Solver::assign(Literal l) {
        Variable var = sat::var(l);  
        if(model.find(var.get()) != model.end()){
            TruthValue currentValue = model.at(var.get());
            TruthValue assignedValue = (l.sign() == 1 ? TruthValue::True : TruthValue::False);
            if (currentValue == TruthValue::Undefined) {
                model.at(var.get()) = assignedValue;
                unitLiterals.push_back(l);
                return true;
            } else if (currentValue != assignedValue) {              
                return false; // Literal is already falsified
            }
            return true; // Literal is already satisfied
        }
        return true;
    }

    //cours 7 page 11
    void Solver::DPLL(){
        bool satisfied = false;
        while (!satisfied){
            if (unitPropagate()){
                if (unitLiterals.size() == numVariables){
                    satisfied = true;
                    break;
                } else {
                    
                }
            } else {
                // backtrack
            }
        }
    }


    bool Solver::unitPropagate() {
        unsigned to_propagate = 0;
        std::cout << "Initial unitLiterals: " << unitLiterals << "\n";
        while (to_propagate < unitLiterals.size()) {
            Literal l = unitLiterals[to_propagate].negate();
            bool unit_propagate_L = unitPropagate(l);
            if(!unit_propagate_L){
                return false;
            }
            to_propagate++;
        } 
        return true;
    }



    bool Solver::unitPropagate(Literal l) {
        auto &wl = watches[l];      // watch list des clauses qui regardent l
        std::size_t k = 0;

        while (k < wl.size()) {
            ClausePointer cptr = wl[k];
            Clause &c = *cptr;

            short r = c.getRank(l);                 // quel watcher correspond à l ?
            Literal p = c[c.getIndex(1 - r)];       // l’autre watcher
            std::size_t start = c.getIndex(r);
            std::size_t i = start;

            // Si p est déjà satisfaite, la clause est satisfaite -> rien à faire, on garde la clause ici
            if (satisfied(p)) {
                ++k;
                continue;
            }

            // Chercher un nouveau littéral à watcher (différent de p) qui n’est PAS falsifié
            bool moved = false;
            while (true) {
                i = (i + 1);
                if (i == c.size()) i = 0;
                if (i == start) break;

                Literal cand = c[i];
                if (cand != p && !falsified(cand)) {
                    // Déplacer le watcher r vers cand
                    c.setWatcher(cand, r);

                    // Ajouter la clause dans la watchlist du nouveau littéral
                    watches[cand].push_back(cptr);

                    // Retirer cptr de watches[l] via swap-and-pop
                    wl[k] = wl.back();
                    wl.pop_back();

                    moved = true;
                    break;
                }
            }

            if (moved) {
                // On n’incrémente pas k, car wl[k] est un nouvel élément (swappé)
                continue;
            }

            // Aucun nouveau watcher trouvé : clause devient unitaire ou conflit
            if (falsified(p)) {
                return false; // Conflit : les deux watched literals sont faux
            }

            // Clause unitaire : on doit assigner p vrai
            if (!satisfied(p)) {    // (optionnel) évite doublons si déjà assigné vrai
                assign(p);
                //unitLiterals.push_back(p); // pour propager ensuite
            }

            // On garde la clause dans wl (elle watch toujours l et p)
            ++k;
        }

        return true;
    }



    /*bool Solver::unitPropagate(Literal l){
        std::cout << "watches  INIT : " << watches << "\n";
        for(ClausePointer cptr : watches[l]) {
            std::cout << "cptr: " << cptr << "\n";
            Clause& c = *cptr;
            short r = c.getRank(l);
            Literal p = c[c.getIndex(1-r)];
            std::size_t start = c.getIndex(r);
            std::size_t i = start;

            std::cout << "clause : " << c << "\n"; 
            if (!satisfied(p)) {
                while (true) {
                    i++;

                    if(i == c.size()){
                        i = 0;
                    }
                    if (i == start){
                        break;
                    }
                    if (c[i] != p && !falsified(c[i])) {
                        c.setWatcher(c[i], r);
                        watches[c[i]].push_back(cptr);
                        // Remove cptr from watches[l]
                        auto& watchList = watches[l];
                        auto pos = std::find(watchList.begin(), watchList.end(), cptr);

                        std::cout << "watches size PRE : " << watches.size() << "\n";
                        std::cout << "watches: " << watches << "\n";

                        if (pos != watchList.end()) {
                            watchList.erase(pos);
                        }


                        std::cout << "watches size POST : " << watches.size() << "\n";
                        std::cout << "watches: " << watches << "\n";
                        //watchList.erase(std::remove(watchList.begin(), watchList.end(), cptr), watchList.end());
                        break;
                    }
                }
                if (i == start) {
                    // No new watcher found
                    if (falsified(p)) {
                        return false; // Conflict
                    } else{
                        assign(p);
                        unitLiterals.push_back(p);
                    }
                }
            } 
        }
        return true;
    }*/

} // sat