#ifndef _AUTOQ_SYMBOLICCOMPLEX_PARSER_HH_
#define _AUTOQ_SYMBOLICCOMPLEX_PARSER_HH_

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
        class SymbolicComplexParser;
	}
}

class AUTOQ::Parsing::SymbolicComplexParser {
public:
    SymbolicComplexParser(const std::string &input) : input_(input), index_(0), result(), constMap_(constMap2), used_vars() {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    SymbolicComplexParser(const std::string &input, const std::map<std::string, Complex::Complex> &constMap) : input_(input), index_(0), result(), constMap_(constMap), used_vars() {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    SymbolicComplex getSymbolicComplex() const {
        return result;
    }
    std::set<std::string> getNewVars() const {
        return used_vars;
    }

private:
    std::string input_;
    size_t index_;
    SymbolicComplex result;
    const std::map<std::string, Complex::Complex> &constMap_;
    const std::map<std::string, Complex::Complex> constMap2{}; // empty only for initialization
    std::set<std::string> used_vars;

    void parse() {
        result = parseExpression();
    }

    SymbolicComplex parseExpression() {
        SymbolicComplex left = parseTerm();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '+' || op == '-') {
                index_++;
                SymbolicComplex right = parseTerm();
                if (op == '+') {
                    left = left + right;
                } else {
                    left = left - right;
                }
            } else {
                break;
            }
        }
        return left;
    }

    SymbolicComplex parseTerm() {
        SymbolicComplex left = parseFactor();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '*' || op == '/') {
                index_++;
                SymbolicComplex right = parseFactor();
                if (op == '*') {
                    left = left * right;
                } else if (right.isConst()) {
                    left = left / right.begin()->second;
                } else {
                    THROW_AUTOQ_ERROR("AutoQ does not support this kind of division!");
                }
            } else {
                break;
            }
        }
        return left;
    }

    SymbolicComplex fastPower(SymbolicComplex base, int exponent) {
        assert(exponent >= 0);
        if (exponent == 0) {
            return SymbolicComplex::MySymbolicComplexConstructor(1);
        }
        if (exponent % 2 == 0) {
            SymbolicComplex temp = fastPower(base, exponent / 2);
            return temp * temp;
        } else {
            SymbolicComplex temp = fastPower(base, (exponent - 1) / 2);
            return base * temp * temp;
        }
    }
    SymbolicComplex parseFactor() {
        char nextChar = input_[index_];

        // Handle unary minus
        if (nextChar == '-')
            index_++;

        SymbolicComplex left = parsePrimary();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '^') {
                index_++;
                rational right = parseNumber();
                if (nextChar == '-')
                    return fastPower(left, static_cast<int>(right.numerator())) * -1;
                else
                    return fastPower(left, static_cast<int>(right.numerator()));
            } else {
                break;
            }
        }
        if (nextChar == '-')
            return left * -1;
        else
            return left;
    }

    SymbolicComplex parsePrimary() {
        if (index_ >= input_.length()) {
            THROW_AUTOQ_ERROR("Unexpected end of input");
        }
        if (input_[index_] == '(') {
            index_++;
            SymbolicComplex result = parseExpression();
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
            if (function == "ei2pi") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length() || (!std::isdigit(input_[index_]) && input_[index_] != '-')) {
                        THROW_AUTOQ_ERROR("Invalid argument for A function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for A function");
                    }
                    index_++;
                    // assert(x.imag() == 0);
                    return SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex::Angle(x.to_rational()));
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for A function");
                }
            } else if (function == "sqrt2") {
                return SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex::sqrt2());
            } else if (constMap_.count(function) > 0) {
                return SymbolicComplex::MySymbolicComplexConstructor(constMap_.at(function));
            } else {
                return SymbolicComplex::MySymbolicComplexConstructor(function, used_vars);
            }
        } else if (std::isdigit(input_[index_]) || input_[index_] == '-') {
            return SymbolicComplex::MySymbolicComplexConstructor(Complex::Complex(parseNumber()));
        } else {
            THROW_AUTOQ_ERROR("Unexpected character: " + std::string(1, input_[index_]));
        }
    }

    rational parseNumber() {
        size_t start = index_;
        if (index_ < input_.length() && input_[index_] == '-')
            index_++;
        while (index_ < input_.length() && (std::isdigit(input_[index_]) || input_[index_] == '.')) {
            index_++;
        }
        std::string numStr = input_.substr(start, index_ - start);
        int d = 0;
        for (int i=numStr.length()-1; i>=0; i--) {
            if (numStr.at(i) == '.') {
                d = numStr.length()-1 - i;
                numStr.erase(i, 1);
                break; // assume only one decimal point
            }
        }
        if (numStr.at(0) == '-') {
            while (numStr.at(1) == '0' && numStr.length() >= 3)
                numStr.erase(1, 1);
        } else {
            while (numStr.at(0) == '0' && numStr.length() >= 2)
                numStr.erase(0, 1);
        }
        return rational(boost::multiprecision::cpp_int(numStr), boost::multiprecision::pow(boost::multiprecision::cpp_int(10), d));
    }
};

#endif
