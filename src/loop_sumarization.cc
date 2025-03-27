#include "autoq/loop_sumarization.hh"
#include "autoq/aut_description.hh"
#include "autoq/util/string.hh"

template<typename Symbol>
void execute_loop(std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params, 
                const AUTOQ::regexes& regexes, const std::sregex_iterator& END, std::smatch match_pieces){
    if(params["loop"] == "manual"){
        int start = std::stoi(match_pieces[2].str());
        int end = std::stoi(match_pieces[3].str());
        for(int i = start; i <= end; i++){
            for(const std::string& line : loop_body){
                aut.single_gate_execute(line, regexes, END);
            }
        }
        return;
    }
    if(params["loop"] == "symbolic"){
        symbolic_loop<Symbol>(loop_body, aut, regexes);
    }
}

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction(AUTOQ::Automata<Symbol>& aut, AbstractionMap<Symbol>& alpha){
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T;
    T.name = aut.name + "_loopsum";
    T.finalStates = aut.finalStates;
    T.stateNum = aut.stateNum;
    T.qubitNum = aut.qubitNum;
    T.vars = aut.vars; // ?
    T.constraints = aut.constraints; // ?
    T.hasLoop = aut.hasLoop;
    T.isTopdownDeterministic = aut.isTopdownDeterministic;
    T.transitions = {};
    for(auto& transition : aut.transitions){
        if(transition.first.is_internal()){
            AUTOQ::Symbol::Symbolic symbol = transition.first.symbol().qubit();
            AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
            T.transitions[tag] = transition.second;
        }
        if(transition.first.is_leaf()){
            // symbolic abstract - create new symbolic variables
            // Symbol sym = transition.first.symbol();
            // auto res = alpha.find(sym);
            // if(res == alpha.end()){ // new symbolic variable
            //    for(auto& t : transition.second){
            //        AUTOQ::Complex::SymbolicComplex complex = AUTOQ::Complex::SymbolicComplex();
            //        auto new_symbolic_variable = AUTOQ::Symbol::Symbolic(complex); // is this how its created?
            //        AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({new_symbolic_variable, transition.first.tag()});
            //        alpha[sym] = new_symbolic_variable;
            //
            //        
            //    }
            // }
            // else{
            //    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({res->second, transition.first.tag()});
            //    T.transitions[tag] = transition.second;
            // }
        }
    }
    T.print_aut();
    return T;
}


template<typename Symbol>
void symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::regexes& regexes){
    AbstractionMap<Symbol> alpha;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T = initial_abstraction(aut, alpha);
    

    for(const std::string& line : loop_body){
        T.single_gate_execute(line, regexes, std::sregex_iterator());
    }

}



template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template void execute_loop<AUTOQ::Symbol::Concrete>(std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template void execute_loop<AUTOQ::Symbol::Symbolic>(std::vector<std::string>&,AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template void symbolic_loop<AUTOQ::Symbol::Concrete>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, const AUTOQ::regexes&);
template void symbolic_loop<AUTOQ::Symbol::Symbolic>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, const AUTOQ::regexes&);