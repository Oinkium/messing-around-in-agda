\documentclass{article}

% The following packages are needed because unicode
% is translated (using the next set of packages) to
% latex commands. You may need more packages if you
% use more unicode characters:

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}

% This handles the translation of unicode to latex:

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

% Some characters that are not automatically defined
% (you figure out by the latex compilation errors you get),
% and you need to define:

\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}

% Add more as you need them (shouldn't happen often).

% Using '\newenvironment' to redefine verbatim to
% be called 'code' doesn't always work properly. 
% You can more reliably use:

\usepackage{fancyvrb}

\DefineVerbatimEnvironment
  {code}{Verbatim}
  {} % Add fancy options here if you like.

\newcommand{\D}{\AgdaDatatype}
\newcommand{\F}{\AgdaFunction}

\begin{document}

  We start by defining a recursive-inductive type \D{bsPlay} that will encode a Brussels Sprouts position.  The attributes that we keep track of are
  \begin{itemize}
    \item The set of crosses in the position.
    \item The set of edges in the position.
    \item The source and target functions that identify the beginning and ending crosses of each edge (This introduces a direction to our graph which is not part of Brussels Sprouts, but we shall ignore this extra information).
    \item The set of faces in the position.
    \item For each cross, the faces that each crossbar extends into.
  \end{itemize}

  Let $n$ be a fixed integer.  Then our datatype is constructed inductively according to the following rule:
  \begin{itemize}
    \item We start with $n$ crosses and no edges.  There is a unique face and all crossbars extend into that face.
    \item Given any face of the position and any pair of crossbars that extend into that face, we may draw an edge joining the two crossbars and then add a new cross on that edge (so we have actually created two new edges).
  \end{itemize}

  As a preliminary, after importing some standard modules we will need, we define a simple singleton type \D{✶} and use it to construct $n$-element sets.

\begin{code}

module brussels_sprouts where

open import Data.Empty
  renaming (⊥ to ∅)
open import Data.Sum
  renaming (_⊎_ to _⊔_)
open import Data.Product
open import Data.Nat
  renaming (Nat to ℕ)

data ✶ : Set where
  ⋆ : ✶

finiteSet : ℕ → Set
finiteSet (zero) = ∅
finiteSet (succ n) = (finiteSet n) ⊔ ✶

\end{code}

We now start the inductive-recursive definition of the type \D{bsPlay}.  Each position will have attribute functions giving the set of vertices, the set of edges, the source and target functions, the set of faces and the crossbar function.

\begin{code}

data cross : Set where
  north : cross
  south : cross
  east : cross
  west : cross

data bsPlay (n : ℕ) : Set
crosses : bsPlay n → Set
edges : bsPlay n → Set
source : (p : bsPlay n) → edges p → vertices p
target : (p : bsPlay n) → edges p → vertices p
faces : bsPlay n → Set
crossbarFaces : (p : bsPlay n) → crosses p → cross → faces p

data bsPlay (n : ℕ) where
  startingPlay : bsPlay n
  addLine : (p : bsPlay) → (f : faces p) → (v : vertices p) → 

\end{code}

\end{document}

