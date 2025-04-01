#include "autoq/loop_sumarization.hh"
#include "autoq/aut_description.hh"
#include "autoq/util/string.hh"
#include <queue>

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
        aut = symbolic_loop<Symbol>(loop_body, aut, regexes);
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
    int i = 0;
    for(auto& transition : aut.transitions){
        if(transition.first.is_internal()){
            AUTOQ::Symbol::Symbolic symbol = transition.first.symbol().qubit();
            AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
            T.transitions[tag] = transition.second;
        }
        if(transition.first.is_leaf()){
            for(const auto& out : transition.second){
                auto q = out.first;
                auto res = alpha.find(q);
                if(res == alpha.end()){
                    // create new symbolic state
                    AUTOQ::Complex::SymbolicComplex c = AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor("symbolic_" + std::to_string(i++));
                    AUTOQ::Symbol::Symbolic symbol = AUTOQ::Symbol::Symbolic(c);
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                    alpha[q] = symbol;
                } else {
                    // use existing symbolic variable
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({res->second, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                }
            }
        }
    }
    return T;
}

AUTOQ::Symbol::Symbolic eval_mapping(const AUTOQ::Symbol::Symbolic& symbol, SymbolicMap& sigma, SymbolicMap& tau){
    AUTOQ::Symbol::Symbolic result = symbol;
    
    return result;
}

AUTOQ::Automata<AUTOQ::Symbol::Symbolic> refinement(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& T, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref, SymbolicMap& sigma, SymbolicMap& tau){
    // create automata product synchronized by colors
    // a transition is created if Colors1 & Colors2 != 0 (meaning the intersection of colors is not empty)
    // for leaf transitions, eval_mapping() is used to evaluate the symbolic variable in SymbolTag

    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> product;
    product.qubitNum = T.qubitNum;
    product.vars = T.vars;
    product.constraints = T.constraints;
    product.hasLoop = T.hasLoop;
    product.isTopdownDeterministic = T.isTopdownDeterministic;
    product.transitions = {};
    (void)Tref;
    (void)T;
    (void)sigma;
    (void)tau;

    std::vector<std::pair<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag>> worklist;
    for(auto& transition : T.transitions){
        if(transition.first.is_internal()){
            AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag = transition.first;
            product.transitions[tag] = transition.second;
            worklist.push_back({tag, tag});
        }

    }



    return product;
}

template<typename Symbol>
AUTOQ::Automata<Symbol> post_process_sumarization(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref, SymbolicMap& sigma, SymbolicMap& tau){
    AUTOQ::Automata<Symbol> result;
    (void)Tref;
    (void)sigma;
    (void)tau;
    // todo apply mapping back to values we had before


    return result;
}


template<typename Symbol>
AUTOQ::Automata<Symbol> symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::regexes& regexes){
    AbstractionMap<Symbol> alpha;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T = initial_abstraction(aut, alpha);
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> Tref = T;
    SymbolicMap sigma{};
    SymbolicMap tau{};
    
    // start of main summarization loop
    do {

        T.print_aut();
        T = Tref;
        //execute gates
        for(const std::string& line : loop_body){
            T.single_gate_execute(line, regexes, std::sregex_iterator());
        }
        sigma.clear();
        tau.clear();

        // refinement after executing loop body
        Tref = refinement(T, Tref, sigma, tau);
    
    } while(Tref != T); // found fix-point?
    // end of main summarization loop


    // post process the summarization result
    AUTOQ::Automata<Symbol> result = post_process_sumarization<Symbol>(Tref, sigma, tau);
    return result;
}



template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template void execute_loop<AUTOQ::Symbol::Concrete>(std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template void execute_loop<AUTOQ::Symbol::Symbolic>(std::vector<std::string>&,AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template AUTOQ::Automata<AUTOQ::Symbol::Concrete> symbolic_loop<AUTOQ::Symbol::Concrete>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, const AUTOQ::regexes&);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> symbolic_loop<AUTOQ::Symbol::Symbolic>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, const AUTOQ::regexes&);
template AUTOQ::Automata<AUTOQ::Symbol::Concrete> post_process_sumarization<AUTOQ::Symbol::Concrete>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, SymbolicMap&, SymbolicMap&);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> post_process_sumarization<AUTOQ::Symbol::Symbolic>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, SymbolicMap&, SymbolicMap&);
