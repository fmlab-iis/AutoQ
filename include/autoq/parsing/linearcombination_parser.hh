#ifndef _AUTOQ_LinearCombination_PARSER_HH_
#define _AUTOQ_LinearCombination_PARSER_HH_

#include <iostream>
#include <string>
#include <cctype>
#include <cmath>
#include <boost/rational.hpp>
#include "autoq/complex/symbolic_complex.hh"

using AUTOQ::Complex::linear_combination;

namespace AUTOQ
{
	namespace Parsing
	{
        class LinearCombinationParser;
	}
}

class AUTOQ::Parsing::LinearCombinationParser {
public:
    LinearCombinationParser(const std::string& input) : input_(input), index_(0) {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
    }

    linear_combination parse() {
        linear_combination result = parseExpression();
        return result;
    }

private:
    std::string input_;
    size_t index_;

    linear_combination parseExpression() {
        linear_combination left = parseTerm();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '+' || op == '-') {
                index_++;
                linear_combination right = parseTerm();
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

    linear_combination parseTerm() {
        linear_combination left = parseFactor();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '*') {
                index_++;
                linear_combination right = parseFactor();
                // if (op == '*') {
                    left = left * right;
                // } else {
                //     if (!right.isZero()) {
                //         left = left / right;
                //     } else {
                //         throw std::runtime_error(AUTOQ_LOG_PREFIX + "Division by zero");
                //     }
                // }
            } else {
                break;
            }
        }
        return left;
    }

    linear_combination fastPower(linear_combination base, int exponent) {
        assert(exponent >= 0);
        if (exponent == 0) return {{"1", 1}};
        if (exponent % 2 == 0) {
            linear_combination temp = fastPower(base, exponent / 2);
            return temp * temp;
        } else {
            linear_combination temp = fastPower(base, (exponent - 1) / 2);
            return base * temp * temp;
        }
    }
    linear_combination parseFactor() {
        linear_combination left = parsePrimary();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '^') {
                index_++;
                linear_combination right = parsePrimary();
                return fastPower(left, static_cast<int>(right.toInt()));
            } else {
                break;
            }
        }
        return left;
    }

    // template <typename T>
    // boost::rational<boost::multiprecision::cpp_int> others_to_rational(const T &in) {
    //     if constexpr(std::is_convertible_v<T, boost::rational<boost::multiprecision::cpp_int>>)
    //         return boost::rational<boost::multiprecision::cpp_int>(in);
    //     else // temporary conversion for double, may need additional enhancements
    //         return boost::rational<boost::multiprecision::cpp_int>(static_cast<boost::multiprecision::cpp_int>(in * 1000000), 1000000);
    // }
    linear_combination parsePrimary() {
        if (index_ >= input_.length()) {
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "Unexpected end of input");
        }
        if (input_[index_] == '(') {
            index_++;
            linear_combination result = parseExpression();
            if (index_ >= input_.length() || input_[index_] != ')') {
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "Missing closing parenthesis");
            }
            index_++;
            return result;
        } else if (std::isalpha(input_[index_])) {
            size_t start = index_;
            while (index_ < input_.length() && (std::isalpha(input_[index_]) || std::isdigit(input_[index_]) || input_[index_] == '.')) {
                index_++;
            }
            std::string varName = input_.substr(start, index_ - start);
            return {{varName, 1}};
            // if (varName == "ei2pi") {
            // } else {
            //     throw std::runtime_error(AUTOQ_LOG_PREFIX + "Unknown varName: " + varName);
            // }
        } else if (std::isdigit(input_[index_]) || input_[index_] == '-') {
            return {{"1", parseNumber().numerator()}};
            // return linear_combination(parseNumber());
        } else {
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "Unexpected character: " + std::string(1, input_[index_]));
        }
    }

    boost::rational<boost::multiprecision::cpp_int> parseNumber() {
        size_t start = index_;
        while (index_ < input_.length() && (std::isdigit(input_[index_]) || input_[index_] == '.' || input_[index_] == '-')) {
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
        return boost::rational<boost::multiprecision::cpp_int>(boost::multiprecision::cpp_int(numStr), boost::multiprecision::pow(boost::multiprecision::cpp_int(10), d));
    }
};

#endif
