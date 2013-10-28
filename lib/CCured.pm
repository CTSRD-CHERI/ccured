#
#
# Copyright (c) 2001-2002,
#  George C. Necula    <necula@cs.berkeley.edu>
#  Scott McPeak        <smcpeak@cs.berkeley.edu>
#  Wes Weimer          <weimer@cs.berkeley.edu>
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# 1. Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer.
#
# 2. Redistributions in binary form must reproduce the above copyright
# notice, this list of conditions and the following disclaimer in the
# documentation and/or other materials provided with the distribution.
#
# 3. The names of the contributors may not be used to endorse or promote
# products derived from this software without specific prior written
# permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
# IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
# TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
# PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
# OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
# PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#

package CCured;
use strict;

# sm: I can't find a syntax for this that is acceptable to
# all versions of perl.. which is *so* retarded..
#use 5.6_0;     # for 'our' scoping operator

use Carp;
use File::Copy;
use File::Basename;
use Data::Dumper;

use App::Cilly::CilConfig;

$::default_is_merge = 1;

use parent qw(App::Cilly);
use App::Cilly::CilCompiler;

my $base = "$::ccuredhome/src/ccured";
# Select the most recent executable
my $mtime_asm = int((stat("$base.native"))[9]);
my $mtime_byte = int((stat("$base.byte"))[9]);
my $use_debug =
        grep(/--bytecode/, @ARGV) ||
        grep(/--ocamldebug/, @ARGV) ||
        ($mtime_asm < $mtime_byte);
if($use_debug) {
    $ENV{"OCAMLRUNPARAM"} = "b" . $ENV{"OCAMLRUNPARAM"}; # Print back trace
}


my $compiler =
    $base .
    ($use_debug ? ".byte" : ".native");

sub setDefaultArguments {
    my $self = shift;
    $self->{MERGE_INOBJ} = 1;
    $self->{EMITBROWSER} = 1;
    $self->{SHOWSTAGES} = 1;
    $self->{KEEPMERGED} = 1;
    if (defined($ENV{"CILLY_NOCURE"})) {
      $self->{NOCURE} = 1;
      if($self->{VERBOSE}) { print STDERR "Curing disabled by CILLY_NOCURE\n"; }
    }
    push @{$self->{CILARGS}}, "--stages";
}

# We need to customize the collection of arguments
sub collectOneArgument {
    my($self, $arg, $pargs) = @_;
    if($arg eq "--releaselib") {
        $self->{RELEASELIB} = 1; return 1;
    }
    if($arg eq "--nolib") {
        $self->{NOLIB} = 1; return 1;
    }
    if($arg =~ m|--nocure|) {
        $self->{NOCURE} = 1; return 1;
    }
    if($arg =~ m|--allwild|) {
        $self->{ALLWILD} = 1; return 1;
    }
    if($arg eq '--usecil') {
        $self->{USECIL} = 1; return 1;
    }
    if($arg eq '--emitinfer') {
        $self->{EMITINFER} = 1; return 1;
    }
    if($arg =~ m|--browserdir=(.+)$|) {
        $self->{BROWSERDIR} = $1; return 1;
    }
    if($arg eq '--noemitbrowser') {
        $self->{EMITBROWSER} = 0; return 1;
    }
    if($arg =~ m|--browserSourceFileSize=(.+)$|) {
        $self->{BROWSER_SOURCE_FILE_SIZE} = $1; return 1;
    }
    if($arg =~ m|--browserNodeFileSize=(.+)$|) {
        $self->{BROWSER_NODE_FILE_SIZE} = $1; return 1;
    }
    if($arg eq '--optimize') {
        $self->{OPTIMIZE} = 1; return 1;
    }
    if($arg eq '--nogc') {
        $self->{NOGC} = 1;
        return 1;
    }
    if($arg eq '--ocamldebug') {
        $self->{OCAMLDEBUG} = 1; return 1;
    }
    if($arg eq '--optimonly') {
        $self->{OPTIMONLY} = 1;
        push @{$self->{CILARGS}}, $arg;
        return 1;
    }
    if($arg eq '--cxxpp') {
        $self->{CXXPP} = 1; return 1;
    }
    if($arg eq '--useStrings') {
        $self->{USESTRINGS} = 1;
        # Fall through to pass this argument on to CCured
    }
    push @{$self->{CCUREDARGS}}, $arg if $arg eq '--verbose';

    # See if the super class understands this
    return $self->SUPER::collectOneArgument($arg, $pargs);
}

# Customize the help message
sub usage {
    print "ccured [options] [gcc_or_mscl options]\n";
}

sub helpMessage {
    my($self) = @_;
    # Print first the original
    $self->SUPER::helpMessage();
    print <<EOF;

CCured specific options:

  --allwild          All pointers are made WILD
  --nocure           Do not cure

  --usecil           Emit and use the CIL
  --emitinfer        Emit the INFER
  --noemitbrowser    Do not emit pointer-browser data
  --browserSourceSize=n The source-file fragment size
  --optimize         Run the optimizer
  --optimonly        Assumes that the cured file already exists and just
                     optimizes it
  --releaselib       Link with release version of the CCured runtime library
  --nolib            Do not link with the CCured runtime library
  --commPrintLn      Emit #line directives only as comments


 The --leavealone files are not cured.

  All other arguments starting with -- are passed to the CCured engine.

The following are the arguments of the CCured engine
EOF
   my @cmd = ($compiler, '--help');
   $self->runShell(@cmd);
}


sub preprocess_before_cil {
    my($self, $src, $dest, $ppargs) = @_;
    my @args = @{$ppargs};
    if(! $self->{NOCURE}) {
        if($self->{ALLWILD}) {
            push @args, $self->{DEFARG} . "CCURED_ALLWILD";
        }
        if(defined $self->{USESTRINGS}) {
            push @args, $self->{DEFARG} . "CCURED_USE_STRINGS";
        }
        # Force include fixup.h
        unshift @args, $self->forceIncludeArg("$::ccuredhome/include/ccured.h");
        #unshift @args, $self->{INCARG} . $dir . "/lib";
        # Make the preprocessor read cil/include --dsw and matth.
        unshift @args, $self->{INCARG} . $::ccuredhome . "/include";
    }
    return $self->SUPER::preprocess_before_cil($src, $dest, \@args);
}

sub preprocess_after_cil {
    my ($self, $src, $dest, $ppargs) = @_;
    my @args = @{$ppargs};
    push @args, "$self->{DEFARG}CCURED_NO_GC" if $self->{NOGC};
    push @args, "$self->{INCARG}$::ccuredhome/include";
    return $self->SUPER::preprocess_after_cil($src, $dest, \@args);
}

# Find the name of the preprocessed file after CCured processing
sub preprocessAfterOutputFile {
    my($self, $src) = @_;
    return $self->outputFile($src, 'cured.i');
}

# Linking after CIL
sub link_after_cil {
    my ($self, $psrcs, $dest, $ppargs, $ccargs, $ldargs) = @_;

    # Regular linking. Add the library
    my @srcs = @{$psrcs};
    if(! $self->{NOCURE} && ! $self->{NOLIB}) {
        push @srcs,
        "$::ccuredhome/obj/$::archos/ccured_" .
            ($self->{MODENAME} eq "MSLINK" ? "MSVC" : $self->{MODENAME}) .
            ($self->{RELEASELIB} ? "_releaselib" : "_debug") .
                ".$self->{LIBEXT}";
    }
    # !! Not all versions of gcc sypport rdynamic
    if(! $self->{RELEASELIB}) {
        push @{$ldargs}, "-rdynamic";
    }
    my $res = $self->SUPER::link_after_cil(\@srcs,
                                           $dest, $ppargs, $ccargs, $ldargs);
    if($self->{SHOWSTAGES}) {
        print STDERR "Linked the cured program\n";
    }
    return $res;
}


#################### THE CURE

sub afterCil {
    my ($self) = @_;
}

sub CillyCommand {
    my ($self, $psrcs, $dest) = @_;
    my @cmd = ($compiler);

    my ($base, $dir, undef) = fileparse($dest->basis, qr{\.[^.]+});

    my $aftercil;
    if(! $self->{NOCURE}) {
        if($self->{ALLWILD}) {
            push @cmd, '--allwild';
        }
        if($self->{EMITINFER}) {
            push @cmd, '--inferout', "$dir$base.infer.c";
        }
        if($self->{EMITBROWSER}) {
            my $browserdir = "$dir$base.browser"; # A directory
            if(defined $self->{BROWSERDIR}) {
                $browserdir = $self->{BROWSERDIR};
            }
            mkdir $browserdir;
            push @cmd, '--browserout', $browserdir, '--libdir', "$::ccuredhome/lib";
            if(defined($self->{BROWSER_SOURCE_FILE_SIZE})) {
                push @cmd, '--browserSourceFileSize', $self->{BROWSER_SOURCE_FILE_SIZE};
            }
            if(defined($self->{BROWSER_NODE_FILE_SIZE})) {
                push @cmd, '--browserNodeFileSize', $self->{BROWSER_NODE_FILE_SIZE};
            }
            # Copy a few things from the lib dir to the output dir
            foreach my $tocopy ('styles.css', 'browser_blank.html',
                                'pixel.gif', 'bullet.gif',
                                'browser_code.js', 'browser_help.html') {
                my @src_stat = stat("$::ccuredhome/lib/$tocopy");
                my $src_mtime = $src_stat[9];
                my @dst_stat = stat("$browserdir/$tocopy");
                my $dst_mtime = $dst_stat[9];
                if(! -f "$browserdir/$tocopy" || $dst_mtime < $src_mtime) {
                    File::Copy::copy("$::ccuredhome/lib/$tocopy",
                                     "$browserdir/$tocopy");
                  }
            }
        }

	my $cured = $self->cilOutputFile($dest, 'cured.c');
	push @cmd, '--curedout', $cured;

        if($self->{OPTIMIZE}) {
	    $aftercil = $self->cilOutputFile($dest, 'optimcured.c');
            push @cmd, '--doOpt', '--optimout', $aftercil;
        } else {
	    $aftercil = $cured;
        }
    } else {
	$aftercil = $self->cilOutputFile($dest, 'cured.c');
        push @cmd, '--cilout', $aftercil, '--nocure';
    }
    if($self->{CXXPP}) {
        push @cmd, '--doCxxPP', '--cxxppout', "$dir$base.cxx.c";
    }
    if(defined $ENV{OCAMLDEBUG} || $self->{OCAMLDEBUG}) {
        my @idirs = ("src", "src/frontc",
                     "src/ccured", "src/ext", "obj/$::archos");
	my @iflags = map { ('-I', "$::ccuredhome/$_") } @idirs;
        unshift @cmd, 'ocamldebug', '-emacs', @iflags;
    }
    if($self->{VERBOSE}) {
        print "Running CCured ";
        my $fstname = ref $psrcs->[0] ? $psrcs->[0]->{filename} : $psrcs->[0];
        if(@{$psrcs} > 1) {
            print "(in merge mode) on $fstname ... to produce $aftercil->{filename}\n";
        } else {
            print "on $fstname to produce $aftercil->{filename}\n";
        }
    }
    confess "$self produced bad aftercil file: $aftercil"
	unless $aftercil->isa('OutputFile');
    return ($aftercil, @cmd);
}


sub MergeCommand {
    my ($self, $ppsrc, $dir, $base) = @_;

    return ('', $compiler, '--onlyMerge', '--mergeKeepAnnotations');
}

1;
