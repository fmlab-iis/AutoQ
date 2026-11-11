#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE SpanInclusionCli
#include <boost/test/unit_test.hpp>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <stdexcept>
#include <string>
#include <sys/wait.h>
#include <unistd.h>
#include "span_test_util.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#ifndef AUTOQ_CLI_PATH
#define AUTOQ_CLI_PATH "autoq"
#endif
namespace {
std::string quote(const std::string& s) {
    std::string result="'";
    for(char c:s) { if(c=='\'') result+="'\"'\"'"; else result+=c; }
    return result+"'";
}
struct Files {
    std::filesystem::path directory{};
    Files() {
        auto pattern=(std::filesystem::temp_directory_path()/"autoq-span-XXXXXX").string();
        char* p=::mkdtemp(pattern.data());
        if(!p) throw std::runtime_error("mkdtemp failed");
        directory=p;
    }
    ~Files() { std::error_code e; std::filesystem::remove_all(directory,e); }
    std::string write(const std::string& name,const AUTOQ::ConcreteAutomata& a) const {
        const auto path=(directory/name).string();
        std::ofstream f(path);
        f << AUTOQ::Serialization::TimbukSerializer::Serialize(a);
        if(!f) throw std::runtime_error("Fixture write failed");
        return path;
    }
    std::pair<int,std::string> run(const std::string& arguments) const {
        const char* override_path=std::getenv("AUTOQ_TEST_CLI");
        const std::string cli=override_path ? override_path : AUTOQ_CLI_PATH;
        const auto output=(directory/"output.txt").string();
        const auto cmd=quote(cli)+" "+arguments+" >"+quote(output)+" 2>&1";
        const int status=std::system(cmd.c_str());
        std::ifstream f(output);
        const std::string text((std::istreambuf_iterator<char>(f)),std::istreambuf_iterator<char>{});
        return {status!=-1 && WIFEXITED(status) ? WEXITSTATUS(status) : -1,text};
    }
};
}
BOOST_AUTO_TEST_CASE(included_nonincluded_and_resource_outcomes) {
    Files f;
    const auto a=f.write("a.aut",span_test::from_vectors(1,{{1,1}}));
    const auto b=f.write("b.aut",span_test::from_vectors(1,{{1,0},{0,1}}));
    const auto args=quote(a)+" "+quote(b)+" --qubits 1";
    auto [code,text]=f.run("span-inclusion "+args);
    BOOST_CHECK_MESSAGE(code==0,text);
    BOOST_CHECK(text.find("Span inclusion outcome: Included")!=std::string::npos);
    std::tie(code,text)=f.run("span-inclusion "+quote(b)+" "+quote(a)+" --qubits 1");
    BOOST_CHECK_MESSAGE(code==2,text);
    BOOST_CHECK(text.find("Span inclusion outcome: NotIncluded")!=std::string::npos);
    std::tie(code,text)=f.run("span-inclusion "+args+" --max-basis-runs 1");
    BOOST_CHECK_MESSAGE(code==3,text);
    BOOST_CHECK(text.find("Span inclusion outcome: ResourceLimit")!=std::string::npos);
    std::tie(code,text)=f.run("span-inclusion "+quote(a)+" "+quote(b)+" --qubits=-1");
    BOOST_CHECK_MESSAGE(code==4,text);
    BOOST_CHECK(text.find("Span inclusion outcome: UnsupportedInput")!=std::string::npos);
}
BOOST_AUTO_TEST_CASE(help_and_invalid_arguments) {
    Files f;
    auto [code,text]=f.run("span-inclusion --help");
    BOOST_CHECK_MESSAGE(code==0,text);
    BOOST_CHECK(text.find("--qubits")!=std::string::npos);
    std::tie(code,text)=f.run("span-inclusion");
    BOOST_CHECK(code!=0);
    BOOST_CHECK(text.find("Span inclusion outcome:")==std::string::npos);
}
BOOST_AUTO_TEST_CASE(existing_print_still_works) {
    Files f;
    auto path=f.write("existing.aut",span_test::from_vectors(1,{{1,0}}));
    auto [code,text]=f.run("print "+quote(path));
    BOOST_CHECK_MESSAGE(code==0,text);
}
