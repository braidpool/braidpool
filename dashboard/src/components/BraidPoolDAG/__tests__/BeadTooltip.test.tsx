import '@testing-library/jest-dom';
import React from 'react';
import { render, screen } from '@testing-library/react';
import BeadTooltip from '../BeadTooltip';

const hash = (c: string) => c.repeat(64);

describe('BeadTooltip', () => {
  it('shows bead details for an HWP bead', () => {
    render(
      <BeadTooltip
        bead={{
          id: hash('a'),
          parents: [hash('b')],
          children: ['1', '2', '3', '4', '5', '6', '7'].map(hash),
        }}
        cohortIndex={3}
        hwpPosition={2}
      />
    );

    expect(screen.getByText(hash('a'))).toBeInTheDocument();
    expect(screen.getByText('Cohort Index:').parentElement).toHaveTextContent(
      'Cohort Index: 3'
    );
    expect(screen.getByText('Yes (Position: 2)')).toHaveClass('text-green-400');
    expect(screen.getByText('Parents (1):')).toBeInTheDocument();
    expect(screen.getByText('bbbbbbbbbbbb...bbbbbbbb')).toBeInTheDocument();
    expect(screen.getByText('Children (7):')).toBeInTheDocument();
    expect(screen.getByText('555555555555...55555555')).toBeInTheDocument();
    expect(
      screen.queryByText('666666666666...66666666')
    ).not.toBeInTheDocument();
    expect(screen.getByText('... and 2 more')).toBeInTheDocument();
  });

  it('shows genesis and leaf labels for a bead with no links', () => {
    render(
      <BeadTooltip
        bead={{ id: hash('c'), parents: [], children: [] }}
        cohortIndex={undefined}
        hwpPosition={null}
      />
    );

    expect(screen.getByText('Cohort Index:').parentElement).toHaveTextContent(
      'Cohort Index: N/A'
    );
    expect(screen.getByText('No')).toHaveClass('text-red-500');
    expect(screen.getByText('None (Genesis)')).toBeInTheDocument();
    expect(screen.getByText('None (Leaf bead)')).toBeInTheDocument();
  });
});
