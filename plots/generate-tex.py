#!/usr/bin/env python3
import os, sys, itertools

COLORS = 'red green blue cyan magenta yellow black gray brown lime olive orange pink purple teal violet darkgray lightgray'.split(' ')
MARKS = 'o asterisk star oplus otimes square square* triangle triangle* diamond diamond* pentagon pentagon* - | oplus* otimes*'.split(' ')

def to_valid_tex_cmd(s):
    numbers = ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine']
    for n, v in enumerate(numbers):
        s = s.replace(str(n), v)
    return s.replace(' ', '').replace('-', '').replace('_', '')


def generate_legend_and_regression(color, mark, xlabel, ylabel, name):
    variables = {'linear': ('a', 'b'),
                 'quadratic': ('a', 'b', 'c'),
                 'cubic': ('a', 'b', 'c', 'd'),
                 'exponential': ('a', 'b')}
    ylabels = ylabel.split('-regression-')
    short_ylabel = ylabels[0]
    regression_kinds = []
    for ylabel_part in ylabels[1:]:
        ylabel_part_parts = ylabel_part.split('-')
        regression_kinds.append(ylabel_part_parts[0])
        if len(ylabel_part_parts) > 1:
            short_ylabel += '-' + '-'.join(ylabel_part_parts[1:])
    def print_poly(regression_kind):
        vs = variables[regression_kind]
        ret = ''
        for e, v in reversed(list(enumerate(reversed(vs)))):
            print_sign_str = '[print sign]' if e != len(vs) - 1 else ''
            ret += fr'\pgfmathprintnumber{print_sign_str}{{\csname pgfplotstable{short_ylabel}-{regression_kind}regression{v}\endcsname}}'
            if e == 0: pass
            else:
                ret += fr' \cdot x' # \left(\text{{{xlabel}}}\right)'
                if e != 1: ret += fr'^{{{e}}}'
                ret += ' '
        return ret
    ret = fr'''
        \addlegendentry{{{short_ylabel}}}'''
    if short_ylabel.endswith('-sys'): # skip system time regressions, since they're not very useful, and can make gnuplot fail to converge
        return ret
    for regression_kind in regression_kinds:
        variables_str = '\n'.join(fr'        \expandafter\xdef\csname pgfplotstable{short_ylabel}-{regression_kind}regression{v}\endcsname{{\pgfplotstableregression{v}}}' for v in variables[regression_kind])
        if regression_kind == 'linear':
            ret += fr'''
        \addplot[no markers, color={color}] table[x=param-{xlabel},y={{create col/linear regression={{y={ylabel}}}}}]{{{name}.txt}};
{variables_str}
        \addlegendentry{{${print_poly(regression_kind)}$}}'''
        elif regression_kind in ('quadratic', 'cubic', 'exponential'):
            ret += fr'''
        \addplot{regression_kind}regression[no markers, color={color}, smooth][x=param-{xlabel},y={ylabel}]{{{name}.txt}};
{variables_str}'''
            if regression_kind in ('quadratic', 'cubic'):
                ret += fr'''
        \addlegendentry{{${print_poly(regression_kind)}$}}'''
            elif regression_kind == 'exponential':
                ret += fr'''
        \addlegendentry{{$\pgfmathprintnumber{{\csname pgfplotstable{short_ylabel}-{regression_kind}regressiona\endcsname}}\exp\left(\pgfmathprintnumber{{\csname pgfplotstable{short_ylabel}-{regression_kind}regressionb\endcsname}}\cdot\left(\text{{{xlabel}}}\right)\right)$}}'''
        else:
            raise Exception('Invalid regression_kind: %s (not in %s)' % (regression_kind, ', '.join(sorted(variables.keys()))))
    return ret

def generate_tex(name, txt_lines):
    header = txt_lines[0].strip().split(' ')
    ylabels = [h for h in header[1:] if not h.startswith('param-')]
    cols = [line.strip().split(' ')[i] for line in txt_lines[1:] for i in range(len(header))]
    extra_params_descr = ', '.join(u"%s \u2208 {%s}" % (h, ', '.join(sorted(set(col)))) for h, col in zip(header[1:], cols[1:]) if h.startswith('param-'))
    if extra_params_descr != '': extra_params_descr = ' ' + extra_params_descr
    ylabels_dict = {ylabel:float(val) for ylabel, val in zip(txt_lines[0].strip().split(' '), txt_lines[-1].strip().split(' '))}
    contents = ''.join(txt_lines)
    short_name = to_valid_tex_cmd(name)
    if len(ylabels) < 1: raise Exception('Invalid header with not enough columns: %s' % repr(txt_lines[0]))
    if not header[0].startswith('param-'): raise Exception('Invalid header: first column %s does not start with param-' % header[0])
    xlabel = header[0][len('param-'):]
    plots = [fr'        \addplot[only marks,mark={mark},color={color}] table[x=param-{xlabel},y={ylabel}]{{{name}.txt}};'
             + generate_legend_and_regression(color=color, mark=mark, xlabel=xlabel, ylabel=ylabel, name=name)
             for mark, color, ylabel
             in zip(itertools.cycle(MARKS),
                    itertools.cycle(COLORS),
                    reversed(sorted(ylabels, key=ylabels_dict.get)))]
    plots_txt = '\n'.join(plots)
    return r'''
\begin{figure*}
  \begin{tikzpicture}
    \begin{filecontents*}{%(name)s.txt}
%(contents)s
\end{filecontents*}
    \begin{axis}[xlabel=%(xlabel)s,
        ylabel=time (s),
        legend pos=outer north east,
        width=0.95\textwidth,
        axis lines=left,
        xmin=0,
        ymin=0,
        scaled x ticks=false,
        scaled y ticks=false]
%(plots_txt)s
    \end{axis}
  \end{tikzpicture}
  \caption{timing-%(name)s%(extra_params_descr)s} \label{fig:timing-%(name)s}
\end{figure*}''' % locals(), contents

if __name__ == '__main__':
    if len(sys.argv) not in (4, 5):
        print(f'USAGE: {sys.argv[0]} NAME INPUT OUTPUT [TABLE_FILE]')
    name, infile, outfile, table_file = sys.argv[1:] if len(sys.argv) == 5 else sys.argv[1:] + [None]
    with open(infile, 'r') as f:
        intext = f.readlines()
    res, table = generate_tex(name, intext)
    with open(outfile, 'w') as f:
        f.write(res)
    if table_file is not None:
        with open(table_file, 'w') as f:
            f.write(table)
