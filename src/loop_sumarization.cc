#include "autoq/loop_sumarization.hh"

template<typename Symbol>
void execute_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params){
    if(params["loop"] == "manual"){
        for(const std::string& line : loop_body){
            //single_gate_execute(line, aut);
        }
    }
    if(params["loop"] == "symbolic"){
        //symbolic_loop(loop_body, aut);
    }
}

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction(AUTOQ::Automata<Symbol>& aut, AbstractionMap<Symbol>& alpha){
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T;
    T.name = aut.name + "_loopsum";
    T.finalStates = aut.finalStates;
    T.stateNum = aut.stateNum;
    T.qubitNum = aut.qubitNum;
    T.name = aut.name + "_loopsum";
    T.finalStates = aut.finalStates;
    T.stateNum = aut.stateNum;
    T.qubitNum = aut.qubitNum;
    T.vars = aut.vars; // ?
    T.constraints = aut.constraints; // ?
    T.hasLoop = aut.hasLoop;
    T.isTopdownDeterministic = aut.isTopdownDeterministic;
    for(auto& transition : aut.transitions){
        if(transition.first.is_internal()){
            auto sym = transition.first.symbol();
            T.transitions[sym] = transition.second;
        }
        if(transition.first.is_leaf()){
            // symbolic abstract - create new symbolic variables
            auto sym = transition.first.symbol();
            auto res = alpha.find(sym);
            if(res == alpha.end()){ // new symbolic variable
                auto new_symbolic_variable = AUTOQ::Symbol::Symbolic();
                alpha[sym] = new_symbolic_variable;
                T.transitions[new_symbolic_variable] = transition.second;
            }
            else{
                T.transitions[res->second] = transition.second;
            }
        }
    }
    return T;
}


template<typename Symbol>
void symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut){
    AbstractionMap<Symbol> alpha;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T = initial_abstraction(aut, alpha);
    

}