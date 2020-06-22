#!/usr/bin/env python3
import os, sys

COLORS = 'red green blue cyan magenta yellow black gray brown lime olive orange pink purple teal violet darkgray lightgray'.split(' ')
MARKS = 'o asterisk star oplus otimes square square* triangle triangle* diamond diamond* pentagon pentagon* - | oplus* otimes*'.split(' ')

def to_valid_tex_cmd(s):
    numbers = ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine']
    for n, v in enumerate(numbers):
        s = s.replace(str(n), v)
    return s.replace(' ', '').replace('-', '').replace('_', '')

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
    plots = [fr'''        \addplot[only marks,mark={mark},color={color}] table[x=param-{xlabel},y={ylabel}]{{\{short_name}}};
        \addlegendentry{{{ylabel}}}'''
             for mark, color, ylabel
             in zip(MARKS + ['*'] * len(ylabels),
                    COLORS + ['black'] * len(ylabels),
                    reversed(sorted(ylabels, key=ylabels_dict.get)))]
    plots_txt = '\n'.join(plots)
    return r'''
\begin{figure*}
  \begin{tikzpicture}
    \pgfplotstableread{
%(contents)s
}{\%(short_name)s}
    \begin{axis}[xlabel=$%(xlabel)s$,
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
