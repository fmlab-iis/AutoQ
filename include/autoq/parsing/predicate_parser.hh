#ifndef _AUTOQ_PREDICATE_PARSER_HH_
#define _AUTOQ_PREDICATE_PARSER_HH_

#include <iostream>
#include <string>
#include <cctype>
#include <cmath>
#include <boost/rational.hpp>
#include "autoq/complex/complex.hh"
#include "autoq/complex/symbolic_complex.hh"

using AUTOQ::Complex::Complex;
using AUTOQ::Complex::SymbolicComplex;

typedef boost::rational<boost::multiprecision::cpp_int> rational;

namespace AUTOQ {
	namespace Parsing {
        class PredicateParser;
	}
}

class AUTOQ::Parsing::PredicateParser {
public:
    // PredicateParser(const std::string &input) : input_(input), index_(0), result(), constMap_(constMap2) {
    //     std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
    //     parse();
    // }
    PredicateParser(const std::string &input, const std::string &targetVar_) : input_(input), index_(0), result(), resultVar(), targetVar(targetVar_) {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    std::string getSMTexpression() const {
        if (resultVar == targetVar) {
            return result;
        } else {
            return "";
        }
    }

private:
    std::string input_;
    size_t index_;
    std::string result;
    std::string resultVar;
    const std::string &targetVar;
    // const std::map<std::string, Complex::Complex> predicateMap2{}; // empty only for initialization

    void parse() {
        result = parseOR();
    }

    std::string parseOR() {
        std::string left = parseAND();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '|') {
                index_++;
                std::string right = parseAND();
                left = "(or " + left + " " + right + ")";
            } else {
                break;
            }
        }
        return left;
    }

    std::string parseAND() {
        std::string left = parseNOT();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '&') {
                index_++;
                std::string right = parseNOT();
                left = "(and " + left + " " + right + ")";
            } else {
                break;
            }
        }
        return left;
    }

    std::string parseNOT() {
        char nextChar = input_[index_];
        if (nextChar == '!') { // Handle unary negation
            index_++;
            return "(not " + parseNOT() + ")";
        } else
            return parseComparison();
    }

    std::string parseComparison() {
        /*SymbolicComplex*/ std::string left = parseExpression();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '=') {
                index_++;
                /*SymbolicComplex*/ std::string right = parseExpression();
                return "(= " + left + " " + right + ")";
                // return std::string("(and ")
                //         + "(= " + left/*.realToSMT()*/ + " " + right/*.realToSMT()*/ + ")"
                //         + "(= " + left/*.imagToSMT()*/ + " " + right/*.imagToSMT()*/ + ")"
                //     + ")";
            } else if (op == '<') {
                index_++;
                /*SymbolicComplex*/ std::string right = parseExpression();
                return "(< " + left/*.realToSMT()*/ + " " + right/*.realToSMT()*/ + ")";
            } else if (op == '>') {
                index_++;
                /*SymbolicComplex*/ std::string right = parseExpression();
                return "(> " + left/*.realToSMT()*/ + " " + right/*.realToSMT()*/ + ")";
            } else {
                break;
            }
        }
        THROW_AUTOQ_ERROR("Invalid boolean formula.");
    }

    /*SymbolicComplex*/ std::string parseExpression() {
        /*SymbolicComplex*/ std::string left = parseTerm();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '+' || op == '-') {
                index_++;
                /*SymbolicComplex*/ std::string right = parseTerm();
                if (op == '+') {
                    left = "(+ " + left + " " + right + ")";
                } else {
                    left = "(- " + left + " " + right + ")";
                }
            } else {
                break;
            }
        }
        return left;
    }

    /*SymbolicComplex*/ std::string parseTerm() {
        /*SymbolicComplex*/ std::string left = parseFactor();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '*' || op == '/') {
                index_++;
                /*SymbolicComplex*/ std::string right = parseFactor();
                if (op == '*') {
                    left = "(* " + left + " " + right + ")";
                } else /*if (right.isConst())*/ {
                    left = "(/ " + left + " " + right/*.begin()->second*/ + ")";
                }/* else {
                    THROW_AUTOQ_ERROR("AutoQ does not support this kind of division!");
                }*/
            } else {
                break;
            }
        }
        return left;
    }

    // SymbolicComplex fastPower(SymbolicComplex base, int exponent) {
    //     assert(exponent >= 0);
    //     if (exponent == 0) {
    //         return SymbolicComplex::MySymbolicComplexConstructor(1);
    //     }
    //     if (exponent % 2 == 0) {
    //         SymbolicComplex temp = fastPower(base, exponent / 2);
    //         return temp * temp;
    //     } else {
    //         SymbolicComplex temp = fastPower(base, (exponent - 1) / 2);
    //         return base * temp * temp;
    //     }
    // }
    /*SymbolicComplex*/ std::string parseFactor() {
        char nextChar = input_[index_];

        // Handle unary minus
        if (nextChar == '-')
            index_++;

        /*SymbolicComplex*/ std::string left = parsePrimary();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '^') {
                THROW_AUTOQ_ERROR("AutoQ does not support power operation in predicates!");
                // index_++;
                // rational right = parseNumber();
                // if (nextChar == '-')
                //     return fastPower(left, static_cast<int>(right.numerator())) * -1;
                // else
                //     return fastPower(left, static_cast<int>(right.numerator()));
            } else {
                break;
            }
        }
        if (nextChar == '-')
            return "(- " + left + ")"; // * -1;
        else
            return left;
    }

    /*SymbolicComplex*/ std::string parsePrimary() {
        if (index_ >= input_.length()) {
            THROW_AUTOQ_ERROR("Unexpected end of input");
        }
        if (input_[index_] == '(') {
            index_++;
            /*SymbolicComplex*/ std::string result = parseExpression();
            if (index_ >= input_.length() || input_[index_] != ')') {
                THROW_AUTOQ_ERROR("Missing closing parenthesis");
            }
            index_++;
            return result;
        } else if (std::isalpha(input_[index_])) {
            size_t start = index_;
            while (index_ < input_.length() && (std::isalpha(input_[index_]) || std::isdigit(input_[index_]) || input_[index_] == '.')) {
                index_++;
            }
            std::string function = input_.substr(start, index_ - start);
            /*if (function == "ei2pi") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length() || (!std::isdigit(input_[index_]) && input_[index_] != '-')) {
                        THROW_AUTOQ_ERROR("Invalid argument for ei2pi function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for ei2pi function");
                    }
                    index_++;
                    // assert(x.imag() == 0);
                    return SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex::Angle(x.to_rational()));
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for ei2pi function");
                }
            } else if (function == "eipi") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length() || (!std::isdigit(input_[index_]) && input_[index_] != '-')) {
                        THROW_AUTOQ_ERROR("Invalid argument for eipi function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for eipi function");
                    }
                    index_++;
                    // assert(x.imag() == 0);
                    return SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex::Angle(x.to_rational() / 2));
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for eipi function");
                }
            } else*/ if (function == "real") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length()) {
                        THROW_AUTOQ_ERROR("Invalid argument for real function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for real function");
                    }
                    index_++;
                    return "real(" + x + ")"; // "R"; // x.real();
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for real function");
                }
            } else if (function == "imag") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length()) {
                        THROW_AUTOQ_ERROR("Invalid argument for imag function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for imag function");
                    }
                    index_++;
                    return "imag(" + x + ")"; // x + "I"; // x.imag();
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for imag function");
                }
            // } else if (function == "sqrt2") {
            //     return SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex::sqrt2());
            } else if (targetVar == function) {
                if (resultVar.empty()) {
                    resultVar = function;
                } else if (resultVar != function) {
                    THROW_AUTOQ_ERROR("Two predicates are independent and cannot be detected!");
                }
                return "$"; // SymbolicComplex::MySymbolicComplexConstructor(constMap_.at(function));
            } else { // may be some variables used in the precondition
                return function; // SymbolicComplex::MySymbolicComplexConstructor(function);
            }
        } else if (std::isdigit(input_[index_]) || input_[index_] == '-') {
            return parseNumber(); // SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex(parseNumber()));
        } else {
            THROW_AUTOQ_ERROR("Unexpected character: " + std::string(1, input_[index_]));
        }
    }

    /*rational*/ std::string parseNumber() {
        size_t start = index_;
        if (index_ < input_.length() && input_[index_] == '-')
            index_++;
        while (index_ < input_.length() && (std::isdigit(input_[index_]) || input_[index_] == '.')) {
            index_++;
        }
        std::string numStr = input_.substr(start, index_ - start);
        return numStr;
        // int d = 0;
        // for (int i=numStr.length()-1; i>=0; i--) {
        //     if (numStr.at(i) == '.') {
        //         d = numStr.length()-1 - i;
        //         numStr.erase(i, 1);
        //         break; // assume only one decimal point
        //     }
        // }
        // if (numStr.at(0) == '-') {
        //     while (numStr.at(1) == '0' && numStr.length() >= 3)
        //         numStr.erase(1, 1);
        // } else {
        //     while (numStr.at(0) == '0' && numStr.length() >= 2)
        //         numStr.erase(0, 1);
        // }
        // return rational(boost::multiprecision::cpp_int(numStr), boost::multiprecision::pow(boost::multiprecision::cpp_int(10), d));
    }
};

#endif
