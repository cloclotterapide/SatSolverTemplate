/**
* @author Tim Luchterhand
* @date 26.11.24
* @brief
*/

#include "basic_structures.hpp"
#include "util/exception.hpp"

namespace sat {
    // @TODO implementation here

    Variable::Variable(unsigned val) {
        id = val;
    }

    unsigned Variable::get() const {
        return id;
    }

    bool Variable::operator==(Variable other) const {
        return (id==other.id);
    }

    Literal::Literal(unsigned val) {
        id = val;
    }

    unsigned Literal::get() const {
        return id;
    }

    Literal Literal::negate() const {
        if (id%2 == 0){
            return Literal(id+1);
        }
        else{
            return  Literal(id-1);
        }
    }

    short Literal::sign() const {
        if (id%2 == 0){
            return -1;
        }
        else{
            return 1;
        }
    }

    bool Literal::operator==(Literal other) const {
        return id == other.id;
    }

    Literal pos(Variable x) {
        return Literal(x.get()*2+1);
    }

    Literal neg(Variable x) {
        return Literal(x.get()*2);
    }

    Variable var(Literal l) {
        return Variable(l.get()/2);
    }
}
