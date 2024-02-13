#include <cassert>
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/util/convert.hh"

/**
 * @brief  Trim whitespaces from a string (both left and right)
 */
std::string AUTOQ::String::trim(const std::string& str)
{
	std::string result = str;

	// trim from start
	result.erase(result.begin(), std::find_if(result.begin(), result.end(),
		[](int ch) {return !std::isspace(ch);}));

	// trim from end
	result.erase(std::find_if(result.rbegin(), result.rend(),
		[](int ch) {return !std::isspace(ch);}).base(), result.end());

	return result;
}

/**
 * @brief  Split a string at a delimiter
 */
std::vector<std::string> AUTOQ::String::split_delim(
	const std::string&   str,
	char                 delim)
{
	std::vector<std::string> result;

	std::string::size_type pos = 0;
	std::string::size_type prev = 0;
	while ((pos = str.find(delim, prev)) != std::string::npos)
	{
		result.push_back(str.substr(prev, pos - prev));
		prev = pos + 1;
	}

	// To get the last substring (or only, if delimiter is not found)
	result.push_back(str.substr(prev));

	return result;
}


/**
 * @brief  Read the first word from a string
 *
 * Reads the first word from a string and removes it from there
 */
std::string AUTOQ::String::read_word(std::string& str)
{
	std::string::iterator end(std::find_if(str.begin(), str.end(),
		[](int ch) { return std::isspace(ch);}));
	std::string result(str.begin(), end);

	str.erase(str.begin(), end);
	str = AUTOQ::String::trim(str);
	return result;
}


/**
 * @brief  Does the string contain a whitespace?
 */
bool AUTOQ::String::contains_whitespace(const std::string& str)
{
	return str.end() != std::find_if(str.begin(), str.end(), [](int ch) { return std::isspace(ch);});
}


/**
 * @brief  Parse a token of the form <string>:<number> or <string>
 */
std::pair<std::string, int> AUTOQ::String::parse_colonned_token(std::string str)
{
	str = AUTOQ::String::trim(str);

	// no space inside
	assert(!AUTOQ::String::contains_whitespace(str));

	size_t colon_pos = str.find(":");
	if (std::string::npos == colon_pos)
	{	// no colon found
		return std::make_pair(str, -1);
	}
	else
	{	// colon found
		std::string number_str = str.substr(colon_pos + 1);

		return std::make_pair(str.substr(0, colon_pos), AUTOQ::Util::Convert::FromString<int>(number_str));
	}
}