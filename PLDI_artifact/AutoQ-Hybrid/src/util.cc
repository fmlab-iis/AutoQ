/*****************************************************************************

 *
 *  Description:
 *    Implementation of miscellaneous utility gadgets.
 *
 *****************************************************************************/

// VATA headers
#include <vata/vata.hh>
#include <vata/util/util.hh>

// Standard library headers
#include <fstream>

std::string VATA::Util::ReadFile(const std::string& fileName)
{
	std::ifstream t(fileName);
	if (!t)
	{	// in case the file could not be open
		throw std::runtime_error("Error opening file " + fileName);
	}

	std::string str;

	t.seekg(0, std::ios::end);
	str.reserve(t.tellg());
	t.seekg(0, std::ios::beg);

	str.assign((std::istreambuf_iterator<char>(t)),
		std::istreambuf_iterator<char>());

	return str;
}

bool VATA::Util::ShellCmd(const std::string &cmd, std::string &result) {
    char buffer[512];
    result = "";

    // Open pipe to file
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        return false;
    }

    // read till end of process:
    while (!feof(pipe)) {
        // use buffer to read and add to result
        if (fgets(buffer, sizeof(buffer), pipe) != NULL)
            result += buffer;
    }

    pclose(pipe);
    return true;
}

// VATA::AutBase::StateDict VATA::Util::CreateProductStringToStateMap(
// 	const VATA::AutBase::StateDict& lhsCont,
// 	const VATA::AutBase::StateDict& rhsCont,
// 	const AutBase::ProductTranslMap& translMap)
// {
// 	typedef VATA::AutBase::StateDict StateDict;

// 	StateDict result;

// 	for (auto mapElem : translMap)
// 	{
// 		const auto& key = mapElem.first;

// 		StateDict::ConstIteratorBwd itLhs;
// 		if ((itLhs = lhsCont.FindBwd(key.first)) == lhsCont.EndBwd())
// 		{
// 			assert(false);  // fail gracefully
// 		}

// 		StateDict::ConstIteratorBwd itRhs;
// 		if ((itRhs = rhsCont.FindBwd(key.second)) == rhsCont.EndBwd())
// 		{
// 			assert(false);  // fail gracefully
// 		}

// 		std::string prodStateStr = '[' + itLhs->second + "_1|" +
// 			itRhs->second + "_2]";
// 		result.insert(std::make_pair(prodStateStr, mapElem.second));
// 	}

// 	return result;
// }


// VATA::AutBase::StateDict VATA::Util::CreateUnionStringToStateMap(
// 	const VATA::AutBase::StateDict& lhsCont,
// 	const VATA::AutBase::StateDict& rhsCont,
// 	const AutBase::StateToStateMap* translMapLhs,
// 	const AutBase::StateToStateMap* translMapRhs)
// {
// 	typedef VATA::AutBase::StateType StateType;
// 	typedef VATA::AutBase::StateToStateMap StateToStateMap;
// 	typedef VATA::AutBase::StateDict StateDict;

// 	StateDict result;

// 	for (auto dictElem : lhsCont)
// 	{
// 		StateType state = dictElem.second;
// 		if (translMapLhs != nullptr)
// 		{	// in case there should be translation
// 			StateToStateMap::const_iterator itTransl;
// 			if ((itTransl = translMapLhs->find(state)) == translMapLhs->end())
// 			{
// 				assert(false);    // fail gracefully
// 			}

// 			state = itTransl->second;
// 		}

// 		if (!result.insert(std::make_pair(dictElem.first + "_1", state)).second)
// 		{	// in the case there is already something
// 			assert(false);
// 		}

// 	}

// 	for (auto dictElem : rhsCont)
// 	{
// 		StateType state = dictElem.second;
// 		if (translMapRhs != nullptr)
// 		{	// in case there should be translation
// 			StateToStateMap::const_iterator itTransl;
// 			if ((itTransl = translMapRhs->find(state)) == translMapRhs->end())
// 			{
// 				assert(false);    // fail gracefully
// 			}

// 			state = itTransl->second;
// 		}

// 		if (!result.insert(std::make_pair(dictElem.first + "_2", state)).second)
// 		{	// in the case there is already something
// 			assert(false);
// 		}
// 	}

// 	return result;
// }
