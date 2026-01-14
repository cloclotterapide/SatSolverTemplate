/**
* @author Tim Luchterhand
* @date 26.11.24
* @brief
*/

#include <cassert>
#include <algorithm>

#include "Clause.hpp"
#include "util/exception.hpp"

namespace sat {
    //TODO implementation here

    Clause::Clause(std::vector<Literal> literals){
        this->literals = literals;
        firstWatcherIndex = literals.size() > 0 ? 0 : NULL;
        secondWatcherIndex = literals.size() > 1 ? 1 : NULL;
    }

    short Clause::getRank(Literal l) const {
        if (l == literals.at(firstWatcherIndex)) {
            return 0;
        } else if (l == literals.at(secondWatcherIndex)){
            return 1;
        } else {
            return -1;
        }
    }

    std::size_t Clause::getIndex(short rank) const {
        for ( std :: size_t idx = 0; idx < literals.size() ; ++idx ){
            if (rank == 0){
                if (idx == firstWatcherIndex){
                    return idx;
                }
            }else{
                if (idx == secondWatcherIndex){
                    return idx;
                }
            }
        }
    }


    bool Clause::setWatcher(Literal l, short watcherNo) {
        for (std :: size_t idx = 0; idx < literals.size() ; ++idx ){
            if (l == literals.at(idx)){
                if (watcherNo == 0){
                    firstWatcherIndex = idx;
                }
                else {
                    secondWatcherIndex = idx;
                }
                return true;
            }
        }
        return false;
    }

    auto Clause::begin() const -> std::vector<Literal>::const_iterator {
        return literals.begin();
    }

    auto Clause::end() const -> std::vector<Literal>::const_iterator {
        return literals.end();
    }

    bool Clause::isEmpty() const {
        return literals.empty();
    }

    Literal Clause::operator[](std::size_t index) const {
        return literals.at(index);
    }

    std::size_t Clause::size() const {
        return literals.size();
    }

    Literal Clause::getWatcherByRank(short rank) const {
        if (rank == 0){
            return literals.at(firstWatcherIndex);
        } else{
            return literals.at(secondWatcherIndex);
        }
    }

    bool Clause::sameLiterals(const Clause &other) const {
        if (literals.size() == other.literals.size()){
            auto literalsCopy = literals;
            auto otherLiteralsCopy = other.literals;

            std::sort(literalsCopy.begin(),literalsCopy.end(),[](Literal A, Literal B){return A.get() > B.get();});
            std::sort(otherLiteralsCopy.begin(),otherLiteralsCopy.end(),[](Literal A, Literal B){return A.get() > B.get();});

            for ( std :: size_t idx = 0; idx < literals.size() ; ++idx ){
                if (literalsCopy[idx] != otherLiteralsCopy[idx]){
                    return false;
                }
            }
            return true;

        }else{
            return false;
        }
    }

}
