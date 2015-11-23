#!/usr/bin/perl

use strict;
use warnings;

my $in_version = 0;
my $in_domain = 0;

sub close_domain {
  if ($in_domain) {
    print "        </itemizedlist>\n";
    print "      </listitem>\n";
    $in_domain = 0;
  }
}

sub close_version {
  if ($in_version) {
    close_domain;
    print "    </itemizedlist>\n";
    print "  </listitem>\n";
    $in_version = 0;
  }
}

print "<itemizedlist>\n";

my $has_git = (-d "../.git");

open(my $in, "<", "../NEWS") or die "Can't open NEWS: $!";

while (<$in>) {
  if (/^Version ([^:]+):/) {
    close_version;
    my $version = $1;
    my $date = "";
    $date = qx(git log -1 --pretty="%ai" gappa-$version) if ($has_git);
    print "  <listitem>\n";
    if ($date =~ /^([^ ]+).*$/) {
      print "    <para>Version $version ($1)</para>\n";
    } else {
      print "    <para>Version $version</para>\n";
    }
    print "    <itemizedlist>\n";
    $in_version = 1
  } elsif (/^ [*] (.+)/) {
    close_domain;
    $in_domain = 1;
    print "      <listitem>\n";
    print "        <para>$1</para>\n";
    print "        <itemizedlist>\n";
  } elsif (/^   - (.+)/) {
    print "          <listitem><para><![CDATA[$1]]></para></listitem>\n";
  }
}

close_version;
print "</itemizedlist>\n";
