#!/usr/bin/perl

use File::Slurp;
use File::Basename;

use warnings;
use strict;

my $tex = shift @ARGV;
my $dir = shift @ARGV;
my $session = shift @ARGV;

my $root = read_file($tex);
my @uses = ($root =~ /\\theory{([a-zA-Z0-9-]*)}/g);

printf "$tex refers to %d theories.\n", scalar @uses;
my %index;
@index{@uses} = (0..$#uses);

my @global_theories = qw!HOLCF Nominal2 ../Nominal2/Nominal2 ~~/src/HOL/Library/AList Library/AList Lifting Main!;
my %global;
@global{@global_theories} = (0..$#global_theories);

my @real_uses = (read_file($session) =~ /\\input{([a-zA-Z0-9-]*)\.tex}/g);

my %seen;
for my $base (@real_uses) {
	next if $base =~ /^[a-z]/;
	#printf "Checking %s\n", $base;
	printf "%s is not mentioned in %s!\n", $base, $tex unless exists $index{$base};
	$seen{$base}++;
	my $thy = read_file(sprintf "%s/%s.thy", $dir, $base);
	my ($imports) =  ($thy =~ /imports\s+((?:"?[.~\/a-zA-Z0-9-]+"?\s+)*?)begin/);
	printf "No imports found in %s\n", $base unless $imports;
	next unless $imports;
	my @imports =  ($imports =~ /"?([.~\/a-zA-Z0-9-]+)"?/g);
	printf "0 imports found in %s\n", $base unless @imports;
	# printf "%s has %d imports: %s\n", $base, scalar @imports, (join ", ", @imports);
	for my $import (@imports) {
		next if exists $global{$import};
		printf "%s, imported by %s, is not mentioned in %s!\n", $import, $base, $tex unless exists $index{$import};
		printf "%s, imported by %s, is too late in the document!\n", $import, $base unless $index{$import} < $index{$base};
	}
}

for my $use (@uses) {
	printf "%s is mentioned in %s, but not used!\n", $use, $tex unless exists $seen{$use};
}
